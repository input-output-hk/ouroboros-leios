# Build with a pinned version of "rust:latest"
FROM 764b84273d2b AS builder

WORKDIR /usr/src/app

COPY sim-rs/ .
COPY libvoidstar.so /usr/lib/

RUN LD_LIBRARY_PATH=/usr/lib RUSTFLAGS=" -Ccodegen-units=1 -Cpasses=sancov-module -Cllvm-args=-sanitizer-coverage-level=3 -Cllvm-args=-sanitizer-coverage-trace-pc-guard -Clink-args=-Wl,--build-id -L/usr/lib -lvoidstar" cargo build --release

RUN LD_LIBRARY_PATH=/usr/lib RUSTFLAGS=" -Ccodegen-units=1 -Cpasses=sancov-module -Cllvm-args=-sanitizer-coverage-level=3 -Cllvm-args=-sanitizer-coverage-trace-pc-guard -Clink-args=-Wl,--build-id -L/usr/lib -lvoidstar" cargo build

FROM debian:bookworm-slim

WORKDIR /root

COPY --from=builder /usr/src/app/target/debug/sim-cli /usr/local/bin/sim-cli-debug
COPY --from=builder /usr/src/app/target/release/sim-cli /usr/local/bin/sim-cli-release
COPY --from=builder /usr/lib/libvoidstar.so /usr/lib/libvoidstar.so

COPY network.yaml .
COPY config.yaml .
COPY singleton_release.sh /opt/antithesis/test/v1/simple_release/singleton_driver_simulate.sh
COPY singleton_debug.sh /opt/antithesis/test/v1/simple_debug/singleton_driver_simulate.sh

RUN apt-get update
RUN apt-get install -y python3 pip

RUN pip install antithesis cffi --break-system-packages

COPY entrypoint.py /entrypoint.py

CMD ["/entrypoint.py"]
