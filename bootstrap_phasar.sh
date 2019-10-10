#!/bin/bash
set -e
# echo "Installing PhASAR dependencies..."
# echo "Installing dependencies from sources..."
# sudo apt-get update
# sudo apt-get install -y zlib1g zlib1g-dev sqlite3 libsqlite3-dev python3 doxygen graphviz python python-dev python3-pip python-pip libxml2 libxml2-dev libncurses5-dev libncursesw5-dev swig build-essential g++ cmake libedit-dev python-sphinx libcurl4-openssl-dev
# sudo pip install Pygments
# sudo pip install pyyaml

echo "Building PhASAR..."

export CC=/usr/local/bin/clang
export CXX=/usr/local/bin/clang++

mkdir -p build
cd build
cmake -DCMAKE_BUILD_TYPE=Release ..
make -j $(nproc)
echo "PhASAR built successfully."
echo "Installing PhASAR..."
sudo make install
cd ..
echo "PhASAR installed successfully."
