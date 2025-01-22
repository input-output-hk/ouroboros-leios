#!/usr/bin/env jq -crnf

def fmt: . * 1000 | round | . / 1000;

def hist($max; $bins; src): reduce src as $in (
  { bins: $bins, max: $max, hist: [range(0; $bins) | 0] };
  .hist[fmin($in / $max * $bins | floor; $bins - 1)] += 1
);

# takes a hist and transforms it into a CDF string
def cdf: last(.hist[]) as $sum |
  . as { bins: $b, max: $m, hist: $h } |
  ($h | $m / length) as $bin_size |
  $h | keys | reduce .[] as $idx (
    [0, []];
    ($h[$idx] / $sum|fmt) as $y |
    if $y == .[0] then .
    else (.[1] += ["(\($idx * $bin_size|fmt),\($y))"]) | .[0] = $y
    end
  ) | .[1] | "CDF[\(join(","))]";

# `gen`: extract [type, id, time] of data generation, or empty
# `recv`: extract [type, id, time] of data reception, or empty
def read_log(in; gen; recv): reduce in as $in (
  {}; # { [type]: { [id]: [start, latency[]] }}
  def g: ($in | gen) as [$type, $id, $time] |
    setpath([$type, $id]; [$time, []]);
  def r: ($in | recv) as [$type, $id, $time] |
    .[$type][$id] |= . as [$t, $l] | [$t, $l + [$time - $t]];
  g // r // .
) | map_values(
  (map(.[1]|length)|max|debug) as $max | 
  map_values(
    .[1] | select(length == $max) | hist(2; 100; .[])
  )
);

def cumulative: .hist |= [foreach .[] as $in (0; . + $in; .)];

# turns an object with hist values into a single hist
def hist_combine(combine): reduce .[] as $in (
  null;
  if . == null then $in
  else .hist |= . as $h | keys | [.[] | [$h[.], $in.hist[.] // 0] | combine]
  end
);

def hist_min: hist_combine(fmin(.[0]; .[1]));
def hist_max: hist_combine(fmax(.[0]; .[1]));
def hist_avg: (1 / length) as $scale | hist_combine(.[0] + $scale * .[1]);

def min_max: map(cumulative) | {
  min: (hist_min | cdf),
  max: (hist_max | cdf),
  avg: (hist_avg | cdf)
};

def print: . as $all | [
  paths(type == "string") |
  . as $path |
  "\(join("_")) := \($all | getpath($path))"
] | join("\n");

# for Haskell output
#read_log(limit(1000000; inputs);
#  select(.event.tag=="generated")|[.event.kind, .event.id, .time_s];
#  select(.event.tag=="enteredstate")|[.event.kind, .event.id, .time_s])

# for Rust output
read_log(limit(10000000; inputs);
  select(.message.type=="CpuTaskFinished" and .message.task_type=="InputBlockGenerated")|["IB", .message.extra, .time / 1000000000];
  select(.message.type=="CpuTaskFinished" and .message.task_type=="InputBlockValidated")|["IB", .message.extra, .time / 1000000000])

| map_values(min_max)
| print
