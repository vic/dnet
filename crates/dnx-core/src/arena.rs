use crate::error::DnxError;
use crate::slot::Slot;
use std::collections::HashMap;

const MAX_SLOTS: u32 = 1 << 28; // slot_idx = 28 bits → 268M agents

pub(crate) struct Arena {
    slots: Vec<Slot>,
    free: Vec<u32>,
    live_list: Vec<u32>,
    live_pos: HashMap<u32, usize>,
    cap: u32,
}

impl Arena {
    pub(crate) fn new(capacity: u32) -> Arena {
        let cap = capacity.min(MAX_SLOTS);
        let mut slots = Vec::with_capacity(cap as usize);
        slots.push(Slot::EMPTY); // idx 0 = sentinel (never live)
        Arena {
            slots,
            free: Vec::new(),
            live_list: Vec::new(),
            live_pos: HashMap::new(),
            cap,
        }
    }

    pub(crate) fn alloc_slot(&mut self) -> Result<u32, DnxError> {
        let idx = if let Some(idx) = self.free.pop() {
            let old_gen = self.slots[idx as usize].generation;
            self.slots[idx as usize] = Slot::EMPTY;
            self.slots[idx as usize].generation = old_gen.wrapping_add(1);
            idx
        } else {
            let idx = self.slots.len() as u32;
            if idx >= self.cap {
                return Err(DnxError::ArenaCapacityExceeded);
            }
            self.slots.push(Slot::EMPTY);
            idx
        };
        let pos = self.live_list.len();
        self.live_list.push(idx);
        self.live_pos.insert(idx, pos);
        Ok(idx)
    }

    pub(crate) fn retire_slot(&mut self, idx: u32) {
        if let Some(pos) = self.live_pos.remove(&idx) {
            self.live_list.swap_remove(pos);
            if let Some(&moved) = self.live_list.get(pos) {
                self.live_pos.insert(moved, pos);
            }
        }
        self.free.push(idx);
    }

    pub(crate) fn slot(&self, idx: u32) -> &Slot {
        &self.slots[idx as usize]
    }

    pub(crate) fn slot_mut(&mut self, idx: u32) -> &mut Slot {
        &mut self.slots[idx as usize]
    }

    pub(crate) fn live(&self) -> &[u32] {
        &self.live_list
    }

    pub(crate) fn is_live(&self, idx: u32) -> bool {
        self.live_pos.contains_key(&idx)
    }

    /// Reserve n slot indices in advance. Returns base index.
    /// Reserved slots are NOT in live_list yet; use commit_slot to make live.
    pub(crate) fn reserve(&mut self, n: u32) -> Result<u32, DnxError> {
        let base = self.slots.len() as u32;
        if base.checked_add(n).ok_or(DnxError::ArenaCapacityExceeded)? > self.cap {
            return Err(DnxError::ArenaCapacityExceeded);
        }
        for _ in 0..n {
            self.slots.push(Slot::EMPTY);
        }
        Ok(base)
    }

    pub(crate) fn commit_slot(&mut self, idx: u32, slot: Slot) {
        self.slots[idx as usize] = slot;
        let pos = self.live_list.len();
        self.live_list.push(idx);
        self.live_pos.insert(idx, pos);
    }

    pub(crate) fn release_reserved(&mut self, base: u32, used: u32, max: u32) {
        for j in used..max {
            self.free.push(base + j);
        }
    }

    pub(crate) fn slot_count(&self) -> usize {
        self.slots.len()
    }

    /// Encode all slots as flat u32 array for GPU upload (8 u32 per slot).
    /// Field layout matches WGSL struct in rewrite.wgsl.
    pub fn encode_gpu(&self) -> Vec<u32> {
        let mut out = Vec::with_capacity(self.slots.len() * 8);
        for s in &self.slots {
            let w0 = u32::from(s.tag) | (u32::from(s.claim) << 8);
            let w5 = u32::from(s.data) | ((s.delta0 as u16 as u32) << 16);
            let w6 = (s.delta1 as u16 as u32) | (u32::from(s.epoch) << 16);
            out.extend_from_slice(&[w0, s.generation, s.principal, s.aux0, s.aux1, w5, w6, 0u32]);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_skips_sentinel_and_tracks_live() -> Result<(), DnxError> {
        let mut a = Arena::new(8);
        let i = a.alloc_slot()?;
        let j = a.alloc_slot()?;
        let k = a.alloc_slot()?;
        assert_eq!((i, j, k), (1, 2, 3));
        a.retire_slot(j);
        let mut live = a.live().to_vec();
        live.sort_unstable();
        assert_eq!(live, vec![1, 3]);
        Ok(())
    }

    #[test]
    fn reuse_bumps_generation_aba_parity() -> Result<(), DnxError> {
        let mut a = Arena::new(8);
        let i = a.alloc_slot()?;
        let g0 = a.slot(i).generation;
        a.retire_slot(i);
        let j = a.alloc_slot()?;
        assert_eq!(i, j, "tombstone reused");
        assert_eq!(a.slot(j).generation, g0.wrapping_add(1));
        assert_ne!(g0 & 1, a.slot(j).generation & 1, "gen_low parity flips");
        Ok(())
    }

    #[test]
    fn capacity_exceeded_errors() -> Result<(), DnxError> {
        let mut a = Arena::new(3); // sentinel + 2 usable
        a.alloc_slot()?;
        a.alloc_slot()?;
        assert_eq!(a.alloc_slot(), Err(DnxError::ArenaCapacityExceeded));
        Ok(())
    }
}
