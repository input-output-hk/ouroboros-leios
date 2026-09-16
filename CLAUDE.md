# CLAUDE.md — Claude-Specific Instructions

You are assisting with research-and-development exploration and troubleshooting of **Ouroboros Leios**, the Cardano throughput-scaling protocol.

**CRITICAL:** Please begin by reading [AGENTS.md](./AGENTS.md) for project context, mission objectives, goals and constraints, repository blueprint, conventions, and analysis instructions.

## Language

Use American English spelling in all text produced for this project.

## Compaction and memory

When reloading files after compaction, do not reread files in `experiments/` unless there is a conversation underway that directly references them.
