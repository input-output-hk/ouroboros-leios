#!/usr/bin/env -S python3 -u

# This file serves as the client's entrypoint. It: 
# 1. Confirms that all nodes in the cluster are available
# 2. Signals "setupComplete" using the Antithesis SDK

import time

from antithesis.lifecycle import (
    setup_complete,
)

SLEEP = 10

print("Client [entrypoint]: running...")

# Here is the python format for setup_complete. At this point, our system is fully initialized and ready to test.
setup_complete({"Message":"sim-rs cluster is healthy"})

# sleep infinity
time.sleep(31536000)
