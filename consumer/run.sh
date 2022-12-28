#!/bin/bash
set -eux

bash build_binaries.sh
bash start_provider.sh
bash start_consumer.sh
