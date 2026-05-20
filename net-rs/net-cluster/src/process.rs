//! Child process spawning and lifecycle management.
//!
//! Spawns net-node instances as child processes, pipes their output to log
//! files, and handles graceful shutdown.

use std::path::{Path, PathBuf};
use std::process::Stdio;

use tokio::io::AsyncWriteExt;
use tokio::process::{Child, ChildStdin, Command};

/// A running net-node child process.
pub struct ChildNode {
    #[allow(dead_code)]
    pub index: usize,
    pub node_id: String,
    pub child: Child,
    pub stdin: Option<ChildStdin>,
}

/// Manages the set of child net-node processes.
pub struct ProcessManager {
    children: Vec<ChildNode>,
    net_node_bin: PathBuf,
    base_config: String,
    log_dir: PathBuf,
    /// Extra --set overrides forwarded to each net-node process.
    node_overrides: Vec<String>,
}

impl ProcessManager {
    /// Create a new process manager.
    ///
    /// `net_node_bin` is the path to the net-node binary.
    /// `base_config` is the path to the shared base config file.
    /// `log_dir` is where child stdout/stderr logs are written.
    /// `node_overrides` are forwarded as `--set key=value` to each net-node.
    pub fn new(
        net_node_bin: PathBuf,
        base_config: String,
        log_dir: PathBuf,
        node_overrides: Vec<String>,
    ) -> Self {
        Self {
            children: Vec::new(),
            net_node_bin,
            base_config,
            log_dir,
            node_overrides,
        }
    }

    /// Spawn a net-node child process for the given overlay config.
    ///
    /// An optional `extra_config` path is appended as an additional `--config`
    /// layer (loaded after the overlay, so it wins on conflicts).
    pub fn spawn(
        &mut self,
        index: usize,
        node_id: &str,
        overlay_path: &Path,
        extra_config: Option<&Path>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        std::fs::create_dir_all(&self.log_dir)?;

        let log_path = self.log_dir.join(format!("{node_id}.log"));
        let log_file = std::fs::File::create(&log_path)?;
        let stderr_file = log_file.try_clone()?;

        let mut cmd = Command::new(&self.net_node_bin);
        cmd.arg("--config")
            .arg(&self.base_config)
            .arg("--config")
            .arg(overlay_path);
        if let Some(p) = extra_config {
            cmd.arg("--config").arg(p);
        }
        for ov in &self.node_overrides {
            cmd.arg("--set").arg(ov);
        }
        let mut child = cmd
            .stdin(Stdio::piped())
            .stdout(Stdio::from(log_file))
            .stderr(Stdio::from(stderr_file))
            .env(
                "RUST_LOG",
                std::env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string()),
            )
            .kill_on_drop(true)
            .spawn()?;

        let stdin = child.stdin.take();
        tracing::info!("spawned {node_id} (pid {})", child.id().unwrap_or(0));

        self.children.push(ChildNode {
            index,
            node_id: node_id.to_string(),
            child,
            stdin,
        });

        Ok(())
    }

    /// Shut down all child processes gracefully.
    ///
    /// Sends SIGTERM (via kill) to each child and waits up to `timeout` for
    /// them to exit. Any remaining children are force-killed.
    pub async fn shutdown(&mut self, timeout: std::time::Duration) {
        if self.children.is_empty() {
            return;
        }

        tracing::info!("shutting down {} child processes...", self.children.len());

        // Send kill signal to all children.
        for child in &mut self.children {
            if let Err(e) = child.child.kill().await {
                tracing::warn!("failed to kill {}: {e}", child.node_id);
            }
        }

        // Wait for all children with a timeout.
        let wait_all = async {
            for child in &mut self.children {
                match child.child.wait().await {
                    Ok(status) => {
                        tracing::info!("{} exited with {status}", child.node_id);
                    }
                    Err(e) => {
                        tracing::warn!("{} wait error: {e}", child.node_id);
                    }
                }
            }
        };

        if tokio::time::timeout(timeout, wait_all).await.is_err() {
            tracing::warn!("timeout waiting for children to exit");
        }

        self.children.clear();
    }

    /// Check for any children that have exited unexpectedly.
    #[allow(dead_code)]
    pub async fn check_children(&mut self) {
        for child in &mut self.children {
            match child.child.try_wait() {
                Ok(Some(status)) => {
                    tracing::warn!("{} exited unexpectedly with {status}", child.node_id);
                }
                Ok(None) => {} // Still running.
                Err(e) => {
                    tracing::warn!("{} status check error: {e}", child.node_id);
                }
            }
        }
    }

    /// Send a JSON config update to all running children via stdin.
    ///
    /// Writes a single JSON line (terminated by newline) to each child's
    /// stdin pipe. Failures on individual children are logged and skipped.
    pub async fn send_config_update(&mut self, json: &serde_json::Value) {
        let mut line = serde_json::to_string(json).unwrap_or_default();
        line.push('\n');
        let bytes = line.as_bytes();

        for child in &mut self.children {
            if let Some(stdin) = &mut child.stdin {
                if let Err(e) = stdin.write_all(bytes).await {
                    tracing::warn!("failed to send config update to {}: {e}", child.node_id);
                    // stdin broken — drop it so we don't keep trying
                    child.stdin = None;
                }
            }
        }
    }

    /// Number of children currently managed.
    pub fn count(&self) -> usize {
        self.children.len()
    }
}

/// Resolve the net-node binary path.
///
/// If `explicit` is provided, uses that. Otherwise looks next to the current
/// binary for a `net-node` executable.
pub fn resolve_net_node_bin(
    explicit: Option<&str>,
) -> Result<PathBuf, Box<dyn std::error::Error + Send + Sync>> {
    if let Some(path) = explicit {
        let p = PathBuf::from(path);
        if !p.exists() {
            return Err(format!("net-node binary not found at: {}", p.display()).into());
        }
        return Ok(p);
    }

    // Look next to the current executable.
    if let Ok(current_exe) = std::env::current_exe() {
        if let Some(dir) = current_exe.parent() {
            let candidate = dir.join("net-node");
            if candidate.exists() {
                return Ok(candidate);
            }
        }
    }

    // Fall back to PATH lookup.
    if let Ok(output) = std::process::Command::new("which").arg("net-node").output() {
        if output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path.is_empty() {
                return Ok(PathBuf::from(path));
            }
        }
    }

    Err("could not find net-node binary; use --net-node-bin to specify its path".into())
}
