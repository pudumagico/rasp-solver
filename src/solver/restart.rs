pub struct RestartPolicy {
    luby_index: u32,
    base_interval: u64,
    next_restart_at: u64,
    lbd_ema_fast: f64,
    lbd_ema_slow: f64,
    conflicts_since_restart: u64,
}

impl RestartPolicy {
    pub fn new(base: u64) -> Self {
        Self {
            luby_index: 1,
            base_interval: base,
            next_restart_at: base * luby(1),
            lbd_ema_fast: 0.0,
            lbd_ema_slow: 0.0,
            conflicts_since_restart: 0,
        }
    }

    pub fn update_lbd(&mut self, lbd: u32) {
        let v = lbd as f64;
        self.lbd_ema_fast = self.lbd_ema_fast * (31.0 / 32.0) + v * (1.0 / 32.0);
        self.lbd_ema_slow = self.lbd_ema_slow * (4095.0 / 4096.0) + v * (1.0 / 4096.0);
        self.conflicts_since_restart += 1;
    }

    pub fn should_restart(&self, conflicts: u64) -> bool {
        let luby_trigger = conflicts >= self.next_restart_at;
        let glucose_trigger = self.conflicts_since_restart >= 50
            && self.lbd_ema_slow > 0.0
            && self.lbd_ema_fast > 1.1 * self.lbd_ema_slow;
        luby_trigger || glucose_trigger
    }

    pub fn advance(&mut self) {
        self.luby_index += 1;
        self.next_restart_at += self.base_interval * luby(self.luby_index);
        self.conflicts_since_restart = 0;
    }
}

/// Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
fn luby(i: u32) -> u64 {
    let mut size = 1u32;
    let mut seq = 1u32;
    while seq < i {
        seq = 2 * seq + 1;
        size *= 2;
    }
    if seq == i { return size as u64; }
    luby(i - (seq / 2))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn luby_sequence() {
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

    #[test]
    fn glucose_restart_triggers() {
        let mut policy = RestartPolicy::new(100_000);
        for _ in 0..5000 { policy.update_lbd(3); }
        policy.conflicts_since_restart = 50;
        for _ in 0..100 { policy.update_lbd(30); }
        assert!(policy.should_restart(0));
    }
}
