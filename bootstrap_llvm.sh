#!/bin/bash
set -e
# echo "Installing PhASAR dependencies..."
# echo "Installing dependencies from sources..."
# sudo apt-get update
# sudo apt-get install -y zlib1g zlib1g-dev sqlite3 libsqlite3-dev python3 doxygen graphviz python python-dev python3-pip python-pip libxml2 libxml2-dev libncurses5-dev libncursesw5-dev swig build-essential g++ cmake libedit-dev python-sphinx libcurl4-openssl-dev
# sudo pip install Pygments
# sudo pip install pyyaml

echo "Installing LLVM..."
./utils/install-llvm-8.0.0.sh $(nproc) ./
