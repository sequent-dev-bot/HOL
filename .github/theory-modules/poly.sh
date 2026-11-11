#!/bin/bash
# poly.sh [commit]: builds and installs Poly/ML (master by default) in
# $HOME/poly.
set -e
git clone -q https://github.com/polyml/polyml.git polyml
git -C polyml checkout -q "${1:-master}"
git -C polyml log -1 --format='polyml %H %ci'
cd polyml
./configure --prefix="$HOME/poly" > configure.log
make -j4 > make.log 2>&1 || { tail -50 make.log; exit 1; }
make install > install.log
echo "$HOME/poly/bin" >> "$GITHUB_PATH"
