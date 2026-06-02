use crate::tm::Level;

pub fn succ(l: Level) -> Level {
    l + 1
}

pub fn max(i: Level, j: Level) -> Level {
    i.max(j)
}

pub fn le(i: Level, j: Level) -> bool {
    i <= j
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn level_ops() {
        assert_eq!(succ(0), 1);
        assert_eq!(max(2, 5), 5);
        assert!(!le(3, 2));
    }
}
