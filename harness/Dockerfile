FROM rust:1.85-bookworm

RUN apt-get update && apt-get install -y \
    gringo clasp clingo \
    git time \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /workspace
COPY . /workspace
RUN cargo build --release

CMD ["cargo", "test"]
