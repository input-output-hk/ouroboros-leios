use std::{
    collections::{HashMap, VecDeque},
    time::Duration,
};

struct TaskState<T> {
    task: T,
    subtasks: usize,
}

#[derive(Debug, PartialEq, Eq)]
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

    pub fn complete_subtask(&mut self, subtask: Subtask) -> (Option<T>, Option<(Subtask, &T)>) {
        let task = self
            .tasks
            .get_mut(&subtask.task_id)
            .expect("task was already finished");
        task.subtasks -= 1;
        let finished_task = if task.subtasks == 0 {
            self.tasks.remove(&subtask.task_id).map(|s| s.task)
        } else {
            None
        };

        let next_subtask = self.pending_subtasks.pop_front().map(|subtask| {
            let task_state = self.tasks.get(&subtask.task_id).unwrap();
            (subtask, &task_state.task)
        });
        if next_subtask.is_none() {
            self.available_cores = self.available_cores.map(|c| c + 1);
        }

        (finished_task, next_subtask)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::sim::cpu::Subtask;

    use super::CpuTaskQueue;

    #[derive(Debug, PartialEq, Eq)]
    enum CpuTask {
        Something,
    }

    #[test]
    fn should_run_in_parallel_with_no_cores() {
        let mut queue = CpuTaskQueue::new(None, 1.0);
        let (task_id, mut scheduled_subtasks) =
            queue.schedule_task(CpuTask::Something, vec![Duration::from_secs(1); 12]);
        assert_eq!(
            scheduled_subtasks,
            (0..12)
                .map(|subtask_id| Subtask {
                    task_id,
                    subtask_id,
                    duration: Duration::from_secs(1)
                })
                .collect::<Vec<_>>(),
        );
        let final_task = scheduled_subtasks.split_off(11).pop().unwrap();
        for subtask in scheduled_subtasks {
            assert_eq!((None, None), queue.complete_subtask(subtask));
        }
        assert_eq!(
            (Some(CpuTask::Something), None),
            queue.complete_subtask(final_task)
        );
    }

    #[test]
    fn should_run_in_serial_with_one_core() {
        let mut queue = CpuTaskQueue::new(Some(1), 1.0);
        let (_, mut scheduled_subtasks) =
            queue.schedule_task(CpuTask::Something, vec![Duration::from_secs(1); 12]);

        assert_eq!(scheduled_subtasks.len(), 1);
        let mut next_subtask = scheduled_subtasks.pop().unwrap();

        for _ in 0..11 {
            let (None, Some((subtask, CpuTask::Something))) = queue.complete_subtask(next_subtask)
            else {
                panic!("unexpected end");
            };
            next_subtask = subtask;
        }
        assert_eq!(
            (Some(CpuTask::Something), None),
            queue.complete_subtask(next_subtask),
        );
    }

    #[test]
    fn should_run_in_parallel_with_two_cores() {
        let mut queue = CpuTaskQueue::new(Some(1), 1.0);

        let (_, mut scheduled_subtasks) =
            queue.schedule_task(CpuTask::Something, vec![Duration::from_secs(1); 2]);
        assert_eq!(scheduled_subtasks.len(), 1);
        let (None, Some((subtask, CpuTask::Something))) =
            queue.complete_subtask(scheduled_subtasks.pop().unwrap())
        else {
            panic!("unexpected end");
        };
        let (Some(CpuTask::Something), None) = queue.complete_subtask(subtask) else {
            panic!("unexpected continuation");
        };

        let (_, mut scheduled_subtasks) =
            queue.schedule_task(CpuTask::Something, vec![Duration::from_secs(1); 2]);
        assert_eq!(scheduled_subtasks.len(), 1);
        let (None, Some((subtask, CpuTask::Something))) =
            queue.complete_subtask(scheduled_subtasks.pop().unwrap())
        else {
            panic!("unexpected end");
        };
        let (Some(CpuTask::Something), None) = queue.complete_subtask(subtask) else {
            panic!("unexpected continuation");
        };
    }
}
