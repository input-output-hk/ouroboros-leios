use std::{fs, path::Path};

use anyhow::Result;
use sim_core::config::{NodeId, RawConfig, SimConfiguration};

pub fn read_config(
    filename: &Path,
    timescale: Option<u32>,
    trace_nodes: &[usize],
) -> Result<SimConfiguration> {
    let file = fs::read_to_string(filename)?;
    let mut raw_config: RawConfig = toml::from_str(&file)?;
    if let Some(ts) = timescale {
        raw_config.timescale = Some(ts);
    }
    for id in trace_nodes {
        raw_config.trace_nodes.insert(NodeId::new(*id));
    }
    let config: SimConfiguration = raw_config.into();
    config.validate()?;
    Ok(config)
}
