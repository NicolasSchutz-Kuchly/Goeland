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
* This file implements the main logic behind the equality plugin.
**/

package cc

import (
	"fmt"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Core"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Mods/equality/eqStruct"
	"github.com/GoelandProver/Goeland/Search"
	"github.com/GoelandProver/Goeland/Unif"
)

var debug Glob.Debugger

func InitDebugger() {
	debug = Glob.CreateDebugger("plugin.equality")
}

func Enable() {
	SetTryEquality()
	// eqStruct.NewEqStruct = TODO
}

func SetTryEquality() {
	Search.TryEquality = TryEquality
}

// Determine whether equality reasoning is applicable
func TryEquality(atomics_for_dmt Core.FormAndTermsList, st Search.State, new_atomics Core.FormAndTermsList, father_id uint64, cha Search.Communication, node_id int, original_node_id int) bool {
	if !Glob.GetDMTBeforeEq() || len(atomics_for_dmt) == 0 || len(st.GetLF()) == 0 {
		debug(Lib.MkLazy(func() string { return "Try apply equality reasoning !" }))
		if len(new_atomics) > 0 || len(st.GetLF()) == 0 {

			debug(Lib.MkLazy(func() string { return "Equality reasoning is applicable !" }))
			atomics_plus_dmt := append(st.GetAtomic(), atomics_for_dmt...)
			CCstruct := newCCEqualityStruct()
			res_eq, subst_eq, _ := EqualityReasoning(CCstruct, st.GetTreePos(), st.GetTreeNeg(), atomics_plus_dmt.ExtractForms())

			// Resulting substitutions are sent to the proof search
			send_to_proof_search := Lib.NewList[Lib.List[Unif.MixedSubstitution]]()
			for _, substs := range subst_eq {
				local_list := Lib.NewList[Unif.MixedSubstitution]()
				for _, subst := range substs {
					local_list.Append(Unif.MkMixedFromSubst(subst))
				}
				send_to_proof_search.Append(local_list)
			}

			// Closure management
			if res_eq {
				Search.UsedSearch.ManageClosureRule(
					father_id,
					&st,
					cha,
					send_to_proof_search,
					Core.MakeFormAndTerm(
						AST.EmptyPredEq,
						Lib.NewList[AST.Term](),
					),
					node_id,
					original_node_id,
				)
				return true
			}
		}
	}
	return false
}

/*
*
take the cc struct and create a new list of atomics, then check that there are no contradictions.
*/
func testresult(CCstruct CCEqualityStruct, atomic Lib.List[AST.Form]) bool {
	atomicv2, ineq := newAtomics(CCstruct, atomic)

	debug(Lib.MkLazy(func() string {
		//return fmt.Sprintf("\n New atomics: %v ", Lib.ListToString(atomicv2))
		return fmt.Sprintf("\n New atomics: %v \n %v", Lib.ListToString(atomicv2), CCstruct.ToString())
	}))

	if testInequality(ineq) {
		return true
	}

	newtreeneg := Unif.NewNode().MakeDataStruct(atomicv2, false)

	for _, i := range atomicv2.GetSlice() {

		b, _ := newtreeneg.Unify(i)

		if b {
			debug(Lib.MkLazy(func() string {
				return fmt.Sprintf("\n Contradiction with %v ;", i.ToString())
			}))
			return true

		}
	}
	return false

}

/**
* take a list of a != b (ineq)  and return true iff a = b
 */
func testInequality(ineq Lib.List[eqStruct.TermPair]) bool {
	testineq := false
	for _, a := range ineq.GetSlice() {

		testineq = a.GetT1().Equals(a.GetT2())
		if testineq {
			debug(Lib.MkLazy(func() string {
				return fmt.Sprintf("\n CONTRADITION: ~(%v)", a.ToString())
			}))
			break
		}
	}
	return testineq
}

/*
*
create an eqstruct from a list of atomics and a tree pos
*/
func EqStructCreateSimple(CCstruct CCEqualityStruct, tree_pos Unif.DataStructure, atomic Lib.List[AST.Form]) CCEqualityStruct {
	/*create a class for each term */
	for _, a := range atomic.GetSlice() {
		sub := a.GetSubTerms().GetSlice()
		for _, t := range sub {
			CCstruct.AddTerm(t)
		}
	}

	/*add the equalities in the ccstruct*/
	CCstruct = addEqualityConst(CCstruct, tree_pos)

	/*congruence loop , stop when it's stable (a = b => f(a)=f(b))*/
	for CCstruct.congruence() {
	}

	/*Normalize the parents of each class */
	for CCstruct.UpdateParent() {
	}
	return CCstruct

}

/*for each equality , fuse the 2 eqclass from each term in the ccstruct*/
func addEqualityConst(CCstruct CCEqualityStruct, tree_pos Unif.DataStructure) CCEqualityStruct {
	eq := retrieveEqualities(tree_pos.Copy())

	for _, b := range eq {
		eq1 := CCstruct.retrieveEqTerm(b.GetT1())
		eq2 := CCstruct.retrieveEqTerm(b.GetT2())
		CCstruct.union(eq1, eq2)
	}

	return CCstruct
}

/* take a list of atomics and replace the terms by theirs parents in the ccstruct */
func newAtomics(CCstruct CCEqualityStruct, atomic Lib.List[AST.Form]) (Lib.List[AST.Form], Lib.List[eqStruct.TermPair]) {

	atomicsn2 := Lib.List[AST.Form]{}
	pairneq := Lib.List[eqStruct.TermPair]{}

	for _, a := range atomic.GetSlice() {
		switch t := a.(type) {
		case AST.Pred:

			args := Lib.ListCpy(t.GetArgs())
			for x, b := range t.GetArgs().GetSlice() {
				args.Upd(x, find(CCstruct.retrieveEqTerm(b)).term)
			}
			//debug(Lib.MkLazy(func() string { return fmt.Sprintf("test liste args : %s ", Lib.ListToString(args)) }))
			replace := AST.MakePredSimple(t.GetIndex(), t.GetID(), t.GetTyArgs(), args, t.GetMetas())
			atomicsn2.Append(replace)

		case AST.Not:

			switch v := t.GetForm().(type) {
			case AST.Pred:

				args := Lib.ListCpy(v.GetArgs())
				for x, b := range v.GetArgs().GetSlice() {
					args.Upd(x, find(CCstruct.retrieveEqTerm(b)).term)
				}
				//debug(Lib.MkLazy(func() string { return fmt.Sprintf("test liste args : %s ", Lib.ListToString(args)) }))
				formneq := AST.MakePredSimple(t.GetIndex(), v.GetID(), v.GetTyArgs(), args, t.GetMetas())
				replace := AST.MakeNotSimple(t.GetIndex(), formneq, t.GetMetas())
				atomicsn2.Append(replace)
				if formneq.GetID().Equals(AST.Id_eq) {
					t1 := formneq.GetArgs().GetSlice()[0]
					t2 := formneq.GetArgs().GetSlice()[1]
					//debug(Lib.MkLazy(func() string { return fmt.Sprintf("INEQ : %v != %v", t1.ToString(), t2.ToString()) }))
					pairneq.Append(eqStruct.MakeTermPair(t1, t2))
				}
			}

		default:

		}
	}
	return atomicsn2, pairneq
}

/**
* !! ONLY GROUND !!
* Function EqualityReasoning
* Takes atomics
* returns a bool for success and a empty substitution
**/
func EqualityReasoning(CCstruct CCEqualityStruct, tree_pos, tree_neg Unif.DataStructure, atomic Lib.List[AST.Form]) (bool, []Unif.Substitutions, CCEqualityStruct) {
	debug(Lib.MkLazy(func() string { return "Welcome to the CC module ! ! ! " }))
	debug(Lib.MkLazy(func() string { return fmt.Sprintf("Atomics: %v", Lib.ListToString(atomic)) }))

	CCstruct = EqStructCreateSimple(CCstruct, tree_pos, atomic)
	return testresult(CCstruct, atomic), []Unif.Substitutions{}, CCstruct

}
