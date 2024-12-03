# Leios cost model

The Leios cost model computes approximate operating costs and fees for a Leios node.


## Interactive web page

The cost model is embodied in a simple JavaScript application:

- [index.html](index.html)
- [view.css](view.css)
- [src/controller.js](src/controller.js)

Execute `debug.sh` to launch a local server or `build.sh` to build the JavaScript.


## Adga module

The Adga module [CostModel](CostModel.agda) repeates the JavaScript computations but with rigorous checking of the units of measure.

Compare the base scenario of the JavaScript cost model by executing the following:

```console
$ agda --compile Main.agda && ./Main

Resources
  Compute:           6.0 vCPU/month
  Disk:              521.9347105407714 GB/month
  IOPS:              1657.5 IO/s/month
  Network egress:    27468.026039657594 GB/month
  Network interface: 0.39415836334228516 Gb/s/month
Costs
  Compute:          120.0 USD/month
  Disk (amortized): 5073.205386456298 USD/month
  IOPS:             82.875 USD/month
  Network egress:   2746.8026039657593 USD/month
  Total:            8022.8829904220565 USD/month
Metrics
  Cost per transaction: 0.14438981959329794 USD/tx
  Cost per transaction: 0.1925197594577306 ADA/tx
  Retained fees:        14067.958706189473 USD/month
  Retained fees − cost: 6045.075715767416 USD/month
  Retained fees ÷ cost: 175.347923221418 %
```
