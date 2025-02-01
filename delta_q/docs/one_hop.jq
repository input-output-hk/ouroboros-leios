#!/usr/bin/env jq -cnf

def read_rs($emit; key_in; key_out): foreach (range(1; 1000000) | input) as $in (
  [{}];
  (.[0] as $state |
    ($in.message.type | capture("(?<obj>.*)(?<dir>Sent|Received)$")) as { obj: $obj, dir: $dir } |
    ($in.message.id | tostring) as $id |
    if $dir == $emit then
      $state |
      ($in.message | key_out) as $key |
      (getpath([$obj, $key.[], $id]) // empty) as $time |
      delpaths([[$obj, $key.[], $id]]) |
      [., [$obj, ($in.time - $time) / 1000000]]
    else
      $state |
      ($in.message | key_in) as $key |
      setpath([$obj, $key.[], $id]; $in.time) |
      [.]
    end
  ) // [.[0]];
  .[1] // empty
);

def read_hs($store; key_in; $emit; key_out): foreach inputs as $in (
  [{}];
  (.[0] as $state |
    $in.event as { tag: $dir, kind: $obj } |
    select($dir == $store or $dir == $emit) |
    ($in.event.id // $in.event.ids[0]) as $id |
    if $dir == $emit then
      $state |
      ($in.event | key_out) as $key |
      (getpath([$obj, $key.[], $id]) // empty) as $time |
      delpaths([[$obj, $key.[], $id]]) |
      [., [$obj, ($in.time_s - $time) * 1000]]
    else
      $state |
      ($in.event | key_in) as $key |
      setpath([$obj, $key.[], $id]; $in.time_s) |
      [.]
    end
  ) // [.[0]];
  .[1] // empty
);

def histogram(src): reduce src as $in (
  {};
  .[$in[0]][$in[1] | tostring] += 1
);

def histogram_binned($max; $bins; src): reduce src as $in (
  {};
  .[$in[0]][fmin($in[1] / $max * $bins | floor; $bins - 1)] += 1
);

########
# Rust #
########

# delay between receiving a message and sending it on
#histogram(read_rs("Sent"; [.recipient]; [.sender]))

# message propagation time
#histogram(read_rs("Received"; [.sender, .recipient]; [.sender, .recipient]))

###########
# Haskell #
###########

# delay between receiving a message and sending it on
#histogram_binned(1000; 20; read_hs("received"; [.node]; "Sent"; [.sender]))

# message propagation time
histogram_binned(1000; 20; read_hs("Sent"; [.receipient]; "received"; [.node]))
