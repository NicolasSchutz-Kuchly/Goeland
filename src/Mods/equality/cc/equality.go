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
	"strings"

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
		debug(Lib.MkLazy(func() string { return "Try apply quality reasoning !" }))
		if len(new_atomics) > 0 || len(st.GetLF()) == 0 {

			debug(Lib.MkLazy(func() string { return "Equality reasoning is applicable !" }))
			atomics_plus_dmt := append(st.GetAtomic(), atomics_for_dmt...)
			res_eq, subst_eq := EqualityReasoning(st.GetEqStruct(), st.GetTreePos(), st.GetTreeNeg(), atomics_plus_dmt.ExtractForms(), original_node_id)

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
	return false // TODO: return false
}

func EqStructCreate(tree_pos Unif.DataStructure, atomic Lib.List[AST.Form]) *CCEqualityStruct {

	CCstruct := newCCEqualityStruct()

	for _, a := range atomic.GetSlice() {
		sub := a.GetSubTerms().GetSlice()

		for _, t := range sub {

			CCstruct.AddTerm(t)
			//debug(Lib.MkLazy(func() string { return fmt.Sprintf("Atomics: %s", t.ToString()) }))
		}
	}
	CCstruct.initArgsEq()
	//debug(Lib.MkLazy(func() string { return CCstruct.ToString() }))
	eq := retrieveEqualities(tree_pos.Copy())
	for _, a := range eq {
		CCstruct.union(CCstruct.retrieveEqTerm(a.GetT1()), CCstruct.retrieveEqTerm(a.GetT2()))
	}
	loop := true
	for loop {
		loop = CCstruct.congruence()
	}

	return CCstruct

}

// true = incoherence

func testInequality(tree_neg Unif.DataStructure, CCstruct *CCEqualityStruct) bool {

	ineq := retrieveInequalities(tree_neg.Copy())

	testineq := false
	for _, a := range ineq {
		testineq = CCstruct.testSameclass(CCstruct.retrieveEqTerm(a.GetT1()), CCstruct.retrieveEqTerm(a.GetT2()))
		if testineq {
			break
		}
	}
	return testineq
}

/**
* Function EqualityReasoning
* Takes atomics
* creates the problem
* returns a bool for success and the corresponding substitution
**/
func EqualityReasoning(eqStruct eqStruct.EqualityStruct, tree_pos, tree_neg Unif.DataStructure, atomic Lib.List[AST.Form], originalNodeId int) (bool, []Unif.Substitutions) {
	debug(Lib.MkLazy(func() string { return "Welcome to the CC module!" }))
	debug(Lib.MkLazy(func() string { return fmt.Sprintf("Atomics: %v", Lib.ListToString(atomic)) }))
	debug(Lib.MkLazy(func() string {
		var parts []string

		for _, a := range atomic.GetSlice() {
			sub := a.GetSubTerms()

			parts = append(parts, fmt.Sprintf("%v", Lib.ListToString(sub)))
		}

		return fmt.Sprintf("Atomics (subterms): [%s]", strings.Join(parts, ", "))
	}))

	CCstruct := EqStructCreate(tree_pos, atomic)

	debug(Lib.MkLazy(func() string { return CCstruct.ToString() }))
	testineq := testInequality(tree_neg.Copy(), CCstruct)
	debug(Lib.MkLazy(func() string { return fmt.Sprintf("Inegalitée : [%t]", testineq) }))

	atomicsn2 := Lib.List[AST.Form]{}
	for _, a := range atomic.GetSlice() {
		switch t := a.(type) {
		case AST.Pred:

			args := t.GetArgs()
			for x, b := range t.GetArgs().GetSlice() {
				args.Upd(x, CCstruct.find(CCstruct.retrieveEqTerm(b)).resp.term)
			}
			//debug(Lib.MkLazy(func() string { return fmt.Sprintf("test liste args : %s ", Lib.ListToString(args)) }))
			replace := AST.MakePredSimple(t.GetIndex(), t.GetID(), t.GetTyArgs(), args, t.GetMetas())
			atomicsn2.Append(replace)

		case AST.Not:

			switch v := t.GetForm().(type) {
			case AST.Pred:
				args := v.GetArgs()
				for x, b := range v.GetArgs().GetSlice() {
					args.Upd(x, CCstruct.find(CCstruct.retrieveEqTerm(b)).resp.term)
				}
				//debug(Lib.MkLazy(func() string { return fmt.Sprintf("test liste args : %s ", Lib.ListToString(args)) }))
				formneq := AST.MakePredSimple(t.GetIndex(), v.GetID(), v.GetTyArgs(), args, t.GetMetas())
				replace := AST.MakeNotSimple(t.GetIndex(), formneq, t.GetMetas())
				atomicsn2.Append(replace)
			}

		default:

		}

		/**for _, b := range sub.GetSlice() {
			b.(b, CCstruct.find(CCstruct.retrieveEqTerm(b)).resp.term)
		}**/

	}

	debug(Lib.MkLazy(func() string { return fmt.Sprintf("Atomics: %v", Lib.ListToString(atomicsn2)) }))
	return true, []Unif.Substitutions{}
}
