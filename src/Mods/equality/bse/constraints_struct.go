/**
* Copyright 2022 by the authors (see AUTHORS).
*
* Goéland is an automated theorem prover for first order logic.
*
* This software is governed by the CeCILL license under French law and
* abiding by the rules of distribution of free software.  You can  use,
* modify and/ or redistribute the software under the terms of the CeCILL
* license as circulated by CEA, CNRS and INRIA at the following URL
* "http://www.cecill.info".
*
* As a counterpart to the access to the source code and  rights to copy,
* modify and redistribute granted by the license, users are provided only
* with a limited warranty  and the software's author,  the holder of the
* economic rights,  and the successive licensors  have only  limited
* liability.
*
* In this respect, the user's attention is drawn to the risks associated
* with loading,  using,  modifying and/or developing or reproducing the
* software by the user in light of its specific status of free software,
* that may mean  that it is complicated to manipulate,  and  that  also
* therefore means  that it is reserved for developers  and  experienced
* professionals having in-depth computer knowledge. Users are therefore
* encouraged to load and test the software's suitability as regards their
* requirements in conditions enabling the security of their systems and/or
* data to be ensured and,  more generally, to use and operate it in the
* same conditions as regards security.
*
* The fact that you are presently reading this means that you have had
* knowledge of the CeCILL license and that you accept its terms.
**/

/**
* This file contains the type definition of a constraint struct for equality reasoning.
**/

package bse

import (
	"fmt"

	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Unif"
)

type ConstraintStruct struct {
	all_constraints ConstraintList
	subst           Unif.Substitutions
	prec            ConstraintList
}

func (cs ConstraintStruct) getSubst() Unif.Substitutions {
	return cs.subst.Copy()
}
func (cs ConstraintStruct) getPrec() ConstraintList {
	return cs.prec.Copy()
}
func (cs ConstraintStruct) getAllConstraints() ConstraintList {
	return cs.all_constraints
}
func (cs *ConstraintStruct) setSubst(s Unif.Substitutions) {
	cs.subst = s.Copy()
}
func (cs *ConstraintStruct) setPrec(cl ConstraintList) {
	cs.prec = cl.Copy()
}
func (cs *ConstraintStruct) setAllConstraits(cl ConstraintList) {
	cs.all_constraints = cl.Copy()
}
func (cs *ConstraintStruct) addAllConstraints(c Constraint) {
	cs.setAllConstraits(append(cs.getAllConstraints(), c))
}
func (cs ConstraintStruct) isEmpty() bool {
	return cs.getSubst().IsEmpty() && cs.getPrec().isEmpty() && cs.getAllConstraints().isEmpty()
}
func (cs ConstraintStruct) copy() ConstraintStruct {
	return makeConstraintStruct(cs.getAllConstraints(), cs.getSubst(), cs.getPrec())
}
func (cs ConstraintStruct) toString() string {
	return "EQ subst : " + cs.getSubst().ToString() + " - PREC List : " + cs.getPrec().toString() + " - All cst : " + cs.getAllConstraints().toString()
}
func makeEmptyConstraintStruct() ConstraintStruct {
	return ConstraintStruct{makeEmptyConstaintsList(), Unif.MakeEmptySubstitution(), makeEmptyConstaintsList()}
}
func makeConstraintStruct(ac ConstraintList, s Unif.Substitutions, p ConstraintList) ConstraintStruct {
	res := makeEmptyConstraintStruct()
	res.setAllConstraits(ac)
	res.setSubst(s)
	res.setPrec(p)
	return res
}

// appendIfConsistent adds c to the struct if it is consistent with the current
// constraints and LPO ordering. Returns true iff consistent.
// Skips the check (returns true) if c is already recorded.
func (cs *ConstraintStruct) appendIfConsistent(c Constraint) bool {
	if cs.getAllConstraints().contains(c) {
		return true
	}
	ok := cs.isConsistentWith(c)
	debug(Lib.MkLazy(func() string {
		if ok {
			return fmt.Sprintf("%v is consistent — %v", c.toString(), cs.toString())
		}
		return fmt.Sprintf("%v is not consistent — %v", c.toString(), cs.toString())
	}))
	return ok
}

// isConsistentWith checks whether c is compatible with the current substitution
// and PREC list, and updates the struct if the constraint is accepted.
func (cs *ConstraintStruct) isConsistentWith(c Constraint) bool {
	debug(Lib.MkLazy(func() string { return fmt.Sprintf("Constraint : %v", c.toString()) }))
	switch c.getCType() {
	case PREC:
		return cs.isConsistentWithPrec(c)
	case EQ:
		return cs.isConsistentWithEQ(c)
	default:
		debug(Lib.MkLazy(func() string { return "Constraint type unknown" }))
		return false
	}
}

// isConsistentWithPrec handles a PREC constraint.
// After applying the current substitution, two cases arise:
//  1. Ground-comparable by LPO: accept iff respected, then cross-check deferred list.
//  2. Not yet comparable (free metas remain): defer it after a symbolic conflict check.
func (cs *ConstraintStruct) isConsistentWithPrec(c Constraint) bool {
	instantiated := c.copy()
	instantiated.applySubstitution(cs.getSubst())

	respect_lpo, is_comparable := instantiated.checkLPO()
	debug(Lib.MkLazy(func() string {
		return fmt.Sprintf("is_comparable: %v, respect_lpo: %v", is_comparable, respect_lpo)
	}))

	if is_comparable {
		if !respect_lpo {
			return false
		}
		// Satisfied by LPO, but must cross-check deferred constraints:
		// a ground fact like (a ≺ f(X)) could contradict a deferred (f(X) ≺ a).
		return append(cs.getPrec(), instantiated).checkConstraintList()
	}

	// Not yet comparable — defer it if no symbolic contradiction exists.
	newPrec := append(cs.getPrec(), c)
	if !newPrec.checkConstraintList() {
		return false
	}
	cs.setPrec(newPrec)
	cs.addAllConstraints(c)
	return true
}

// isConsistentWithEQ handles an EQ (unification) constraint.
// Checks unifiability against the existing substitution, then verifies that
// the merged substitution does not violate any deferred PREC constraint.
func (cs *ConstraintStruct) isConsistentWithEQ(c Constraint) bool {

	t1, t2 := c.getTP().GetT1(), c.getTP().GetT2()
	// Fast path: isolated unifiability check before touching global state.
	if Unif.AddUnification(t1.Copy(), t2.Copy(), Unif.MakeEmptySubstitution()).Equals(Unif.Failure()) {
		return false
	}

	// Merge with the global substitution.
	subst_all := Unif.AddUnification(t1, t2, cs.getSubst())
	debug(Lib.MkLazy(func() string { return fmt.Sprintf("Subst all: %v", subst_all.ToString()) }))

	if subst_all.Equals(Unif.Failure()) {
		return false
	}
	if subst_all.IsEmpty() {
		return true
	}

	// Ensure the merged substitution doesn't break any deferred PREC constraint.
	debug(Lib.MkLazy(func() string { return "Check if consistent with the whole cl" }))
	if !cs.getPrec().isConsistentWithSubst(subst_all) {
		debug(Lib.MkLazy(func() string { return "Not consistent with the whole cl" }))
		return false
	}

	cs.setSubst(subst_all)
	cs.addAllConstraints(c)
	return true
}
