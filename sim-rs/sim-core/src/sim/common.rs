use std::time::Duration;

use crate::{
    clock::Timestamp,
    config::{NodeId, SimConfiguration},
    events::EventTracker,
    model::CpuTaskId,
    sim::{
        NodeImpl, SimCpuTask,
        cpu::{CpuTaskQueue, Subtask},
    },
};

pub(super) enum NodeEvent<T> {
    NewSlot(u64),
    CpuSubtaskCompleted(Subtask),
    Other(T),
}

pub(super) struct CpuTaskWrapper<Task: SimCpuTask> {
    pub(super) task_type: Task,
    pub(super) start_time: Timestamp,
    pub(super) cpu_time: Duration,
}

/// Schedule a CPU task: creates the wrapper, tracks the scheduling event,
/// and returns the list of immediately-started subtasks.
/// Callers push the returned subtasks into their own event queue.
pub(super) fn schedule_cpu_task<N: NodeImpl>(
    cpu: &mut CpuTaskQueue<CpuTaskWrapper<N::Task>>,
    tracker: &EventTracker,
    node_id: NodeId,
    now: Timestamp,
    task: N::Task,
    config: &SimConfiguration,
) -> Vec<Subtask> {
    let cpu_times = task.times(&config.cpu_times);
    let wrapper = CpuTaskWrapper {
        task_type: task,
        start_time: now,
        cpu_time: cpu_times.iter().sum(),
    };
    let name = wrapper.task_type.name();
    let subtask_count = cpu_times.len();
    let (task_id, subtasks) = cpu.schedule_task(wrapper, cpu_times);
    tracker.track_cpu_task_scheduled(
        CpuTaskId {
            node: node_id,
            index: task_id,
        },
        name.clone(),
        subtask_count,
    );
    for subtask in &subtasks {
        tracker.track_cpu_subtask_started(
            CpuTaskId {
                node: node_id,
                index: subtask.task_id,
            },
            name.clone(),
            subtask.subtask_id,
            subtask.duration,
        );
    }
    subtasks
}

/// Result of completing a CPU subtask.
pub(super) struct CompletedSubtaskResult<N: NodeImpl> {
    /// If a pending subtask was unblocked, it is returned here for scheduling.
    pub(super) next_subtask: Option<Subtask>,
    /// If all subtasks of the parent task finished, the task type is returned.
    pub(super) finished_task: Option<N::Task>,
}

/// Complete a CPU subtask: tracks the next subtask (if any) and the finished task (if done).
/// Callers push next_subtask into their event queue and call node.handle_cpu_task on finished_task.
pub(super) fn complete_cpu_subtask<N: NodeImpl>(
    cpu: &mut CpuTaskQueue<CpuTaskWrapper<N::Task>>,
    tracker: &EventTracker,
    node_id: NodeId,
    now: Timestamp,
    subtask: Subtask,
) -> CompletedSubtaskResult<N> {
    let task_id = CpuTaskId {
        node: node_id,
        index: subtask.task_id,
    };
    let (finished_task, next_subtask) = cpu.complete_subtask(subtask);

    let next = next_subtask.map(|(subtask, task)| {
        tracker.track_cpu_subtask_started(
            CpuTaskId {
                node: node_id,
                index: subtask.task_id,
            },
            task.task_type.name(),
            subtask.subtask_id,
            subtask.duration,
        );
        subtask
    });

    let completed = finished_task.map(|task| {
        let wall_time = now - task.start_time;
        tracker.track_cpu_task_finished(
            task_id,
            task.task_type.name(),
            task.cpu_time,
            wall_time,
            task.task_type.extra(),
        );
        task.task_type
    });

    CompletedSubtaskResult {
        next_subtask: next,
        finished_task: completed,
    }
}
