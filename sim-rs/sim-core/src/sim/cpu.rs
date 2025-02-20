use std::{
    collections::{HashMap, VecDeque},
    time::Duration,
};

struct TaskState<T> {
    task: T,
    subtasks: usize,
    cpu_time: Duration,
}

pub struct Subtask {
    pub task_id: u64,
    pub subtask_id: u64,
    pub duration: Duration,
}

pub struct CpuTaskQueue<T> {
    next_task_id: u64,
    tasks: HashMap<u64, TaskState<T>>,
    pending_subtasks: VecDeque<Subtask>,
    available_cores: Option<u64>,
    multiplier: f64,
}

impl<T> CpuTaskQueue<T> {
    pub fn new(cores: Option<u64>, multiplier: f64) -> Self {
        Self {
            next_task_id: 0,
            tasks: HashMap::new(),
            pending_subtasks: VecDeque::new(),
            available_cores: cores,
            multiplier,
        }
    }

    pub fn schedule_task(&mut self, task: T, durations: Vec<Duration>) -> (u64, Vec<Subtask>) {
        assert!(!durations.is_empty());

        let task_id = self.next_task_id;
        self.next_task_id += 1;
        self.tasks.insert(
            task_id,
            TaskState {
                task,
                subtasks: durations.len(),
                cpu_time: durations.iter().sum(),
            },
        );

        let mut scheduled_subtasks = vec![];
        for (subtask_id, duration) in durations.into_iter().enumerate() {
            let subtask = Subtask {
                task_id,
                subtask_id: subtask_id as u64,
                duration: duration.mul_f64(self.multiplier),
            };
            if self.available_cores.is_none_or(|c| c > 0) {
                self.available_cores = self.available_cores.map(|c| c - 1);
                scheduled_subtasks.push(subtask);
            } else {
                self.pending_subtasks.push_back(subtask);
            }
        }

        (task_id, scheduled_subtasks)
    }

    pub fn complete_subtask(
        &mut self,
        subtask: Subtask,
    ) -> (Option<(T, Duration)>, Option<Subtask>) {
        self.available_cores = self.available_cores.map(|c| c + 1);

        let task = self
            .tasks
            .get_mut(&subtask.task_id)
            .expect("task was already finished");
        task.subtasks -= 1;
        let finished_task = if task.subtasks == 0 {
            self.tasks
                .remove(&subtask.task_id)
                .map(|s| (s.task, s.cpu_time))
        } else {
            None
        };

        let next_subtask = self.pending_subtasks.pop_front();

        (finished_task, next_subtask)
    }
}
