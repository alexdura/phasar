#!/bin/bash
set -e
# echo "Installing PhASAR dependencies..."
# echo "Installing dependencies from sources..."
# sudo apt-get update
# sudo apt-get install -y zlib1g zlib1g-dev sqlite3 libsqlite3-dev python3 doxygen graphviz python python-dev python3-pip python-pip libxml2 libxml2-dev libncurses5-dev libncursesw5-dev swig build-essential g++ cmake libedit-dev python-sphinx libcurl4-openssl-dev
# sudo pip install Pygments
# sudo pip install pyyaml

echo "Installing Boost..."
if [ ! -f boost_1_66_0.tar.gz ]
then
	wget https://dl.bintray.com/boostorg/release/1.66.0/source/boost_1_66_0.tar.gz
fi
if [ ! -d boost_1_66_0/ ]
then
	tar xvf boost_1_66_0.tar.gz
fi
cd boost_1_66_0/
./bootstrap.sh
sudo ./b2 -j $(nproc) install
cd ..
