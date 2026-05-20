//! Shared CLI arguments for scheduler configuration.

use std::collections::HashMap;

use net_core::mux::scheduler::{SchedulerType, TrafficClass};
use net_core::mux::ProtocolId;

/// Scheduler CLI arguments, shared across commands via `#[command(flatten)]`.
#[derive(clap::Args, Debug)]
pub struct SchedulerArgs {
    /// Mux scheduler: round-robin, strict-priority, or priority-wfq (default).
    /// Case-insensitive.
    #[arg(long, default_value = "priority-wfq", value_parser = parse_scheduler_type)]
    pub scheduler: SchedulerType,

    /// Override traffic class for a protocol: <id>,P (Priority) or <id>,<weight> (Default).
    /// Repeatable. Example: --protocol-priority 18,4 --protocol-priority 10,P
    #[arg(long = "protocol-priority")]
    pub protocol_priority: Vec<String>,
}

impl SchedulerArgs {
    /// Parse the `--protocol-priority` values into a map.
    pub fn traffic_class_overrides(&self) -> Result<HashMap<ProtocolId, TrafficClass>, String> {
        let mut map = HashMap::new();
        for arg in &self.protocol_priority {
            let (id_str, class_str) = arg
                .split_once(',')
                .ok_or_else(|| format!("expected <id>,<class> but got: {arg}"))?;
            let id: ProtocolId = id_str
                .parse()
                .map_err(|_| format!("invalid protocol ID: {id_str}"))?;
            let tc = if class_str.starts_with('P') || class_str.starts_with('p') {
                TrafficClass::Priority
            } else {
                let weight: u16 = class_str
                    .parse()
                    .map_err(|_| format!("invalid weight: {class_str}"))?;
                TrafficClass::Default(weight)
            };
            map.insert(id, tc);
        }
        Ok(map)
    }
}

fn parse_scheduler_type(s: &str) -> Result<SchedulerType, String> {
    match s.to_lowercase().as_str() {
        "round-robin" | "roundrobin" | "rr" => Ok(SchedulerType::RoundRobin),
        "strict-priority" | "strictpriority" | "sp" => Ok(SchedulerType::StrictPriority),
        "priority-wfq" | "prioritywfq" | "wfq" => Ok(SchedulerType::PriorityWfq),
        _ => Err(format!(
            "unknown scheduler: {s} (expected round-robin, strict-priority, or priority-wfq)"
        )),
    }
}
