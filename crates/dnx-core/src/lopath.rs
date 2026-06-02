use crate::DnxError;
use std::cmp::Ordering;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LOPath {
    hot: u128,
    warm: Option<u128>,
    cold: Option<u128>,
    frozen: Option<u128>,
    len: u8,
}

impl LOPath {
    pub fn root() -> LOPath {
        LOPath {
            hot: 0,
            warm: None,
            cold: None,
            frozen: None,
            len: 0,
        }
    }

    pub fn extend_right(&self) -> Result<LOPath, DnxError> {
        self.extend_bit(1)
    }

    pub fn extend_left(&self) -> Result<LOPath, DnxError> {
        self.extend_bit(0)
    }

    fn extend_bit(&self, bit: u8) -> Result<LOPath, DnxError> {
        let mut out = self.clone();
        if out.len == 128 {
            match (out.warm, out.cold, out.frozen) {
                (None, _, _) => {
                    out.warm = Some(out.hot);
                }
                (Some(w), None, _) => {
                    out.cold = Some(w);
                    out.warm = Some(out.hot);
                }
                (Some(w), Some(c), None) => {
                    out.frozen = Some(c);
                    out.cold = Some(w);
                    out.warm = Some(out.hot);
                }
                (Some(_), Some(_), Some(_)) => return Err(DnxError::LOPathDepthExceeded),
            }
            out.hot = 0;
            out.len = 0;
        }
        out.hot |= u128::from(bit) << (127 - u32::from(out.len));
        out.len += 1;
        Ok(out)
    }

    pub fn depth(&self) -> usize {
        let full = if self.frozen.is_some() {
            3
        } else if self.cold.is_some() {
            2
        } else if self.warm.is_some() {
            1
        } else {
            0
        };
        full * 128 + self.len as usize
    }

    pub fn is_prefix_of(&self, other: &LOPath) -> bool {
        if self.depth() == 0 {
            return true;
        }
        if self.depth() > other.depth() {
            return false;
        }
        let n = self.n_limbs();
        for (i, limb) in self.all_limbs().enumerate() {
            let other_limb = other.nth_limb(i);
            if i + 1 < n {
                if limb != other_limb {
                    return false;
                }
            } else {
                let shift = 128 - u32::from(self.len);
                if (limb >> shift) != (other_limb >> shift) {
                    return false;
                }
            }
        }
        true
    }

    pub fn prefix_independent(&self, other: &LOPath) -> bool {
        !self.is_prefix_of(other) && !other.is_prefix_of(self)
    }

    pub fn shard_key(&self) -> Option<u8> {
        if self.depth() == 0 {
            None
        } else {
            let first = self.frozen.or(self.cold).or(self.warm).unwrap_or(self.hot);
            Some((first >> 127) as u8)
        }
    }

    fn n_limbs(&self) -> usize {
        1 + usize::from(self.warm.is_some())
            + usize::from(self.cold.is_some())
            + usize::from(self.frozen.is_some())
    }

    fn all_limbs(&self) -> impl Iterator<Item = u128> {
        self.frozen
            .into_iter()
            .chain(self.cold)
            .chain(self.warm)
            .chain(std::iter::once(self.hot))
    }

    fn nth_limb(&self, i: usize) -> u128 {
        self.all_limbs().nth(i).unwrap_or(0)
    }

    /// Serialize hot limb to 4×u32 for GPU upload (depth ≤ 128 only).
    /// Layout: [bits127..96, bits95..64, bits63..32, bits31..0], len.
    pub fn gpu_bits(&self) -> ([u32; 4], u8) {
        let h = self.hot;
        (
            [
                (h >> 96) as u32,
                (h >> 64) as u32,
                (h >> 32) as u32,
                h as u32,
            ],
            self.len,
        )
    }

    /// Reconstruct from GPU 4×u32 bits (hot limb only; depth ≤ 128).
    pub fn from_gpu_bits(hi: u32, mid1: u32, mid0: u32, lo: u32, len: u8) -> LOPath {
        let hot = (u128::from(hi) << 96)
            | (u128::from(mid1) << 64)
            | (u128::from(mid0) << 32)
            | u128::from(lo);
        LOPath {
            hot,
            warm: None,
            cold: None,
            frozen: None,
            len,
        }
    }
}

impl PartialOrd for LOPath {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LOPath {
    fn cmp(&self, other: &Self) -> Ordering {
        for (a, b) in self.all_limbs().zip(other.all_limbs()) {
            match a.cmp(&b) {
                Ordering::Equal => continue,
                ord => return ord,
            }
        }
        self.depth().cmp(&other.depth())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lo(bits: &[u8]) -> Result<LOPath, DnxError> {
        bits.iter().try_fold(LOPath::root(), |p, &b| {
            if b == 0 {
                p.extend_left()
            } else {
                p.extend_right()
            }
        })
    }

    #[test]
    fn depth_counts_bits() -> Result<(), DnxError> {
        assert_eq!(LOPath::root().depth(), 0);
        assert_eq!(lo(&[0, 1, 0])?.depth(), 3);
        Ok(())
    }

    #[test]
    fn lo_order_outer_before_inner() -> Result<(), DnxError> {
        assert!(LOPath::root() < lo(&[0])?);
        assert!(lo(&[0])? < lo(&[0, 1])?);
        Ok(())
    }

    #[test]
    fn lo_order_left_before_right() -> Result<(), DnxError> {
        assert!(lo(&[0])? < lo(&[1])?);
        assert!(lo(&[0, 1, 1])? < lo(&[1])?);
        Ok(())
    }

    #[test]
    fn prefix_independence_iff_disjoint() -> Result<(), DnxError> {
        assert!(lo(&[0])?.prefix_independent(&lo(&[1])?));
        assert!(!lo(&[0])?.prefix_independent(&lo(&[0, 1])?));
        assert!(LOPath::root().is_prefix_of(&lo(&[1, 0, 1])?));
        Ok(())
    }

    #[test]
    fn shard_key_is_first_branch_bit() -> Result<(), DnxError> {
        assert_eq!(LOPath::root().shard_key(), None);
        assert_eq!(lo(&[0, 1, 1])?.shard_key(), Some(0));
        assert_eq!(lo(&[1, 0, 0])?.shard_key(), Some(1));
        Ok(())
    }

    #[test]
    fn limb_promotion_and_overflow() -> Result<(), DnxError> {
        let deep = (0..512).try_fold(LOPath::root(), |p, _| p.extend_right())?;
        assert_eq!(deep.depth(), 512);
        assert_eq!(deep.extend_right(), Err(DnxError::LOPathDepthExceeded));
        Ok(())
    }

    #[test]
    fn shard_key_correct_across_limb_promotion() -> Result<(), DnxError> {
        let mut p = LOPath::root().extend_left()?;
        for _ in 0..200 {
            p = p.extend_right()?;
        }
        assert!(p.depth() > 128);
        assert_eq!(p.shard_key(), Some(0));
        Ok(())
    }
}
