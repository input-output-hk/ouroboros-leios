use crate::models::{Issue, Severity, Topology};

/// Checks for cases where an indirect path between nodes is significantly shorter than the direct connection
pub fn check_triangle_inequality(topology: &Topology) -> Vec<Issue> {
    let mut issues = Vec::new();

    // Check for each direct connection if there's a shorter path through another node
    for (node_id, node) in &topology.nodes {
        for (producer_id, producer) in &node.producers {
            let direct_dist = producer.latency_ms;

            // Check all potential intermediate nodes
            for (intermediate_id, _) in &topology.nodes {
                if intermediate_id == node_id || intermediate_id == producer_id {
                    continue;
                }

                // Check both possible paths through the intermediate node
                let mut indirect_paths = Vec::new();

                // Path 1: node -> intermediate -> producer
                if let Some(first_hop) = node.producers.get(intermediate_id) {
                    if let Some(second_hop) =
                        topology.nodes[intermediate_id].producers.get(producer_id)
                    {
                        indirect_paths.push(first_hop.latency_ms + second_hop.latency_ms);
                    }
                }

                // Path 2: node -> producer -> intermediate -> node
                if let Some(first_hop) = topology.nodes[intermediate_id].producers.get(node_id) {
                    if let Some(second_hop) =
                        topology.nodes[intermediate_id].producers.get(producer_id)
                    {
                        indirect_paths.push(first_hop.latency_ms + second_hop.latency_ms);
                    }
                }

                // If we found any valid indirect paths, check if they're significantly shorter
                if let Some(shortest_indirect) = indirect_paths
                    .iter()
                    .min_by(|a, b| a.partial_cmp(b).unwrap())
                {
                    if *shortest_indirect < direct_dist * 0.8 {
                        issues.push(Issue {
                            severity: Severity::Error,
                            node: node_id.clone(),
                            message: format!(
                                "Path through {} (latency: {:.1}ms) shorter than direct {}->{} (latency: {:.1}ms)",
                                intermediate_id, shortest_indirect, node_id, producer_id, direct_dist
                            ),
                            suggestion: format!(
                                "Review latency of direct connection {}->{} as a {:.1}% shorter path exists through node {}",
                                node_id, producer_id,
                                (direct_dist - *shortest_indirect) / direct_dist * 100.0,
                                intermediate_id
                            ),
                        });
                    }
                }
            }
        }
    }

    issues
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{Location, Node, Producer, Topology};
    use indexmap::IndexMap;

    fn create_test_topology() -> Topology {
        let mut nodes = IndexMap::new();

        // Create a topology with triangle inequality violation:
        // Frankfurt -> Sydney -> Ashburn (total: 200ms)
        // Frankfurt -> Ashburn (direct: 300ms)
        // The path through Sydney should be detected as a violation

        let mut frankfurt_producers = IndexMap::new();
        frankfurt_producers.insert(
            "sydney".to_string(),
            Producer {
                latency_ms: 100.0.try_into().unwrap(),
                bandwidth_bytes_per_second: None,
            },
        );
        frankfurt_producers.insert(
            "ashburn".to_string(),
            Producer {
                latency_ms: 300.0.try_into().unwrap(), // This is too high, should be around 80ms
                bandwidth_bytes_per_second: None,
            },
        );

        let mut sydney_producers = IndexMap::new();
        sydney_producers.insert(
            "ashburn".to_string(),
            Producer {
                latency_ms: 100.0.try_into().unwrap(),
                bandwidth_bytes_per_second: None,
            },
        );

        let mut ashburn_producers = IndexMap::new();
        ashburn_producers.insert(
            "frankfurt".to_string(),
            Producer {
                latency_ms: 300.0.try_into().unwrap(),
                bandwidth_bytes_per_second: None,
            },
        );

        nodes.insert(
            "frankfurt".to_string(),
            Node {
                location: Location::Coordinates([50.1109, 8.6821]),
                stake: 100,
                producers: frankfurt_producers,
                cpu_core_count: Some(8),
            },
        );

        nodes.insert(
            "sydney".to_string(),
            Node {
                location: Location::Coordinates([-33.8688, 151.2093]),
                stake: 0,
                producers: sydney_producers,
                cpu_core_count: Some(4),
            },
        );

        nodes.insert(
            "ashburn".to_string(),
            Node {
                location: Location::Coordinates([39.0438, -77.4874]),
                stake: 200,
                producers: ashburn_producers,
                cpu_core_count: Some(4),
            },
        );

        Topology { nodes }
    }

    #[test]
    fn test_triangle_inequality() {
        let topology = create_test_topology();
        let issues = check_triangle_inequality(&topology);

        // Should find one violation where Frankfurt -> Ashburn direct path
        // is longer than Frankfurt -> Sydney -> Ashburn
        assert_eq!(issues.len(), 1);
        assert!(issues[0].message.contains("frankfurt"));
        assert!(issues[0].message.contains("ashburn"));
        assert_eq!(issues[0].severity, Severity::Error);
    }
}
