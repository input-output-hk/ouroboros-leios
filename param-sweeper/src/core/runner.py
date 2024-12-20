import subprocess
import json
import time
import logging
from pathlib import Path
from typing import Dict, Any, Tuple, Optional
from tqdm import tqdm

logging.basicConfig(level=logging.INFO, 
                   format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

from .types import SimulationConfig, SimulationResult

class SimulationRunner:
    """Handles running individual simulations"""
    
    def __init__(self, base_config_path: Path):
        """Initialize runner with base config path"""
        self.base_config_path = Path(base_config_path)
        self.sim_dir = self.base_config_path.parent.parent
        self.cargo_manifest = self.sim_dir / "Cargo.toml"
        
        logger.info(f"Initialized runner with:")
        logger.info(f"  Base config: {self.base_config_path}")
        logger.info(f"  Sim directory: {self.sim_dir}")
        logger.info(f"  Cargo manifest: {self.cargo_manifest}")
        
        # Build simulation binary once
        logger.info("Building simulation binary...")
        build_cmd = ["cargo", "build", "--release", "--manifest-path", str(self.cargo_manifest)]
        build_result = subprocess.run(build_cmd, capture_output=True, text=True)
        if build_result.returncode != 0:
            logger.error("Build failed:")
            logger.error(build_result.stderr)
            raise RuntimeError("Failed to build simulation binary")
        
        self.sim_binary = self.sim_dir / "target/release/sim-cli"
        logger.info("Build completed successfully")
    
    def run(self, config: SimulationConfig) -> SimulationResult:
        """Run simulation with given configuration"""
        # Write config file
        self._write_config(config)
        logger.info(f"Written config to: {config.config_file}")
        
        # Build command
        cmd = [
            str(self.sim_binary),
            str(config.config_file),
            str(config.output_file)
        ]
        
        logger.info(f"Running simulation: {' '.join(cmd)}")
        
        try:
            # Get total slots from config
            slots_param = config.params.get('slots')
            total_slots = slots_param[0] if isinstance(slots_param, list) else slots_param
            
            # Setup progress bar
            pbar = tqdm(
                total=total_slots,
                desc=f"Simulation {config.iteration}",
                unit="slots",
                bar_format="{desc}: {percentage:3.0f}%|{bar}| {n_fmt}/{total_fmt} slots [{elapsed}<{remaining}, {rate_fmt}]",
                leave=True
            )
            
            # Start simulation process
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                universal_newlines=True,
                bufsize=1
            )
            
            current_slot = 0
            last_file_position = 0
            
            while process.poll() is None:
                # Read new content from output file
                if config.output_file.exists():
                    with open(config.output_file) as f:
                        # Seek to last position
                        f.seek(last_file_position)
                        
                        # Process new lines
                        for line in f:
                            try:
                                event = json.loads(line)
                                if "message" in event and event["message"]["type"] == "Slot":
                                    slot_num = event["message"]["number"]
                                    if slot_num > current_slot:
                                        pbar.update(slot_num - current_slot)
                                        current_slot = slot_num
                                        pbar.refresh()
                            except json.JSONDecodeError:
                                continue
                                
                        # Remember position for next read
                        last_file_position = f.tell()
                
                # Small sleep to prevent busy waiting
                time.sleep(0.1)
            
            # Process any remaining output
            if config.output_file.exists():
                with open(config.output_file) as f:
                    f.seek(last_file_position)
                    for line in f:
                        try:
                            event = json.loads(line)
                            if "message" in event and event["message"]["type"] == "Slot":
                                slot_num = event["message"]["number"]
                                if slot_num > current_slot:
                                    pbar.update(slot_num - current_slot)
                                    current_slot = slot_num
                        except json.JSONDecodeError:
                            continue
            
            # Wait for process to finish
            return_code = process.wait()
            
            # Ensure progress bar shows completion
            if return_code == 0 and current_slot < total_slots:
                pbar.update(total_slots - current_slot)
            pbar.refresh()
            pbar.close()
            print()  # Add newline after progress bar
            
            if return_code == 0:
                logger.info(f"Output written to: {config.output_file}")
                return SimulationResult(config=config, metrics={}, success=True)
            else:
                error = process.stderr.read()
                logger.error(f"Simulation failed with code {return_code}: {error}")
                return SimulationResult(
                    config=config,
                    metrics={},
                    success=False,
                    error=f"Exit code {return_code}: {error}"
                )
                
        except Exception as e:
            logger.error(f"Failed to run simulation: {e}")
            return SimulationResult(
                config=config,
                metrics={},
                success=False,
                error=str(e)
            )
    
    def _write_config(self, config: SimulationConfig) -> None:
        """Write simulation config to file"""
        import toml
        
        # Start with base config
        with open(self.base_config_path) as f:
            full_config = toml.load(f)
            
        # Log the base config
        logger.debug("Base config:")
        for key, value in full_config.items():
            logger.debug(f"  {key}: {value}")
            
        # Update with sweep parameters
        processed_params = {}
        for key, value in config.params.items():
            if isinstance(value, list) and len(value) == 1:
                processed_params[key] = value[0]
            else:
                processed_params[key] = value
                
        # Log the updated params
        logger.debug("Updated params:")
        for key, value in processed_params.items():
            logger.debug(f"  {key}: {value}")
            
        full_config.update(processed_params)
        
        # Write to output directory
        config.config_file.parent.mkdir(parents=True, exist_ok=True)
        with open(config.config_file, 'w') as f:
            toml.dump(full_config, f)
    
    def _run_process(self, config: SimulationConfig) -> Tuple[bool, Optional[str]]:
        """Run simulation process and monitor progress"""
        # Run simulation
        cmd = [
            str(self.sim_binary),
            str(config.config_file),
            str(config.output_file),
        ]
        logger.info(f"Running simulation: {' '.join(cmd)}")
        
        # Start process
        process = subprocess.Popen(
            cmd, 
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1
        )
        
        # Get total slots from config params
        slots_param = config.params.get('slots')
        if isinstance(slots_param, list):
            total_slots = slots_param[0]
        else:
            total_slots = slots_param or 100
        
        # Setup progress bar with better formatting
        pbar = tqdm(
            total=total_slots,
            desc=f"Simulation {config.iteration}",
            unit="slots",
            bar_format="{desc}: {percentage:3.0f}%|{bar}| {n_fmt}/{total_fmt} slots [{elapsed}<{remaining}, {rate_fmt}]",
            leave=True
        )
        
        last_slot = -1
        error_output = []
        
        # Monitor progress
        try:
            while True:
                return_code = process.poll()
                
                # Read output file for progress
                if config.output_file.exists():
                    try:
                        with open(config.output_file) as f:
                            for line in f:
                                try:
                                    event = json.loads(line)
                                    
                                    # Update progress for slot events
                                    if event.get("type") == "Slot":
                                        slot = event.get("number", 0)
                                    elif event.get("message", {}).get("type") == "Slot":
                                        slot = event.get("message", {}).get("number", 0)
                                    else:
                                        continue
                                        
                                    if slot > last_slot:
                                        pbar.n = slot + 1
                                        pbar.refresh()
                                        last_slot = slot
                                        
                                except json.JSONDecodeError:
                                    continue
                    except (IOError, OSError) as e:
                        logger.warning(f"Error reading output file: {e}")
                
                # Check for errors
                if process.stderr:
                    line = process.stderr.readline()
                    if line:
                        error_output.append(line)
                        logger.warning(f"Simulation stderr: {line.strip()}")
                
                # Check if process has finished
                if return_code is not None:
                    break
                
                time.sleep(0.1)
            
            # Ensure 100% at end if successful
            if return_code == 0:
                pbar.n = total_slots
                pbar.refresh()
            
        finally:
            pbar.close()
            print()  # Add spacing after progress bar
            
            # Get any remaining stderr output
            if process.stderr:
                remaining = process.stderr.read()
                if remaining:
                    error_output.append(remaining)
                    logger.warning(f"Final stderr output: {remaining.strip()}")
            
            # Ensure process is terminated
            if process.poll() is None:
                process.terminate()
                process.wait()
        
        success = return_code == 0
        error = ''.join(error_output) if error_output else None
        
        if not success:
            logger.error(f"Simulation process failed with return code {return_code}")
        
        return success, error
    
    def _process_results(self, config: SimulationConfig) -> Dict[str, Any]:
        """Process simulation results into metrics"""
        # This is a placeholder - actual metrics are computed by analyzers
        return {}
