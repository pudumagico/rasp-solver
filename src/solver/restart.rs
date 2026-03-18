pub struct RestartPolicy {
    luby_index: u32,
    base_interval: u64,
    next_restart_at: u64,
}

impl RestartPolicy {
    pub fn new(base: u64) -> Self {
        Self { luby_index: 1, base_interval: base, next_restart_at: base * luby(1) }
    }

    pub fn should_restart(&self, conflicts: u64) -> bool {
        conflicts >= self.next_restart_at
    }

    pub fn advance(&mut self) {
        self.luby_index += 1;
        self.next_restart_at += self.base_interval * luby(self.luby_index);
    }
}

/// Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
/// Uses the standard closed-form: if i is a power of 2, return i; otherwise recurse.
fn luby(i: u32) -> u64 {
    // Find smallest k such that 2^k - 1 >= i
    let mut size = 1u32;
    let mut seq = 1u32;
    while seq < i {
        seq = 2 * seq + 1;
        size *= 2;
    }
    if seq == i {
        return size as u64;
    }
    // Recurse into the subsequence
    luby(i - (seq / 2))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn luby_sequence() {
        // Expected: 1, 1, 2, 1, 1, 2, 4, 1
        let expected = [1, 1, 2, 1, 1, 2, 4, 1];
        for (i, &e) in expected.iter().enumerate() {
            assert_eq!(luby((i + 1) as u32), e, "luby({}) failed", i + 1);
        }
    }

    #[test]
    fn restart_triggers() {
        let mut policy = RestartPolicy::new(100);
        assert!(!policy.should_restart(50));
        assert!(policy.should_restart(100));
        policy.advance();
    }
}
