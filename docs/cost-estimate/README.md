# Leios Node Operating Costs Analysis

## Overview

This document provides a list of cost items that we used for our analysis of the
operational costs associated with running a Leios node. As a baseline
calculation we use Ouroboros Praos for comparisons and different block usage
percentages.

## Cost Items

| Cost Item                             | Unit      | Description                                |
| ------------------------------------- | --------- | ------------------------------------------ |
| [Compute (vCPU)](./01-compute-cpu.md) | $/vCPU/h  | Cost per virtual CPU per hour              |
| [Compute (RAM)](./02-compute-ram.md)  | $/GB/h    | Cost per gigabyte of RAM per hour          |
| [Storage (SSD)](./03-storage.md)      | $/GiB/mo  | Cost per gibibyte of SSD storage per month |
| [Egress](./04-egress.md)              | $/GiB     | Cost per gibibyte of data transferred out  |
| [IOPS](./05-iops.md)                  | $/IOPS/mo | Cost per IOPS per month                    |

Follow the links above to see detailed cost estimates per item.

> [!Note] 
> Storage and data transfer use binary prefixes (GiB = 2³⁰ bytes), while
> RAM uses decimal prefixes (GB = 10⁹ bytes), following industry standards for
> cloud computing.
