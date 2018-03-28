CXX = g++
CXXFLAGS = -Wall -pedantic -std=c++11

Solver: cdcl.cpp
	${CXX} ${CXXFLAGS} -O3 -o $@ $^
