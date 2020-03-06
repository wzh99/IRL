#[derive(Copy, Clone, Debug)]
pub struct Counter {
    /// Number of instructions executed
    pub num: usize,
    /// Time consumed in executing this program
    pub time: usize,
}

impl Counter {
    pub fn new() -> Self { Counter { num: 0, time: 0 } }

    pub fn inc_time(&mut self, clk: usize) { self.time += clk }

    pub fn reset(&mut self) {
        self.num = 0;
        self.time = 0;
    }
}