/*
 * AbstractJoinLattice.h
 *
 *  Created on: 04.08.2016
 *      Author: pdschbrt
 */

#ifndef ANALYSIS_IFDS_IDE_JOINLATTICE_HH_
#define ANALYSIS_IFDS_IDE_JOINLATTICE_HH_


template<typename V>
class JoinLattice {
public:
	virtual ~JoinLattice() = default;
	virtual V topElement() = 0;
	virtual V bottomElement() = 0;
	virtual V join(V lhs, V rhs) = 0;
};

#endif /* ANALYSIS_IFDS_IDE_JOINLATTICE_HH_ */