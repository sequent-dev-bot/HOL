#!/bin/bash
# Builds and installs current Poly/ML master in $HOME/poly.
set -e
git clone -q --depth 1 https://github.com/polyml/polyml.git polyml
git -C polyml log -1 --format='polyml %H %ci'
cd polyml
./configure --prefix="$HOME/poly" > configure.log
make -j4 > make.log 2>&1 || { tail -50 make.log; exit 1; }
make install > install.log
echo "$HOME/poly/bin" >> "$GITHUB_PATH"
