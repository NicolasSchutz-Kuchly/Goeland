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
			res_eq, subst_eq := EqualityReasoning(CCstruct, st.GetTreePos(), st.GetTreeNeg(), atomics_plus_dmt.ExtractForms(), original_node_id)

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

// robinsonUnify implements Robinson's structural unification algorithm on
// Goeland's term representation.  It extends the substitution s in place,
// threading it through recursive calls, and returns Failure() on any clash.
//
// Steps:
//  1. Walk both terms through s to their current representative.
//  2. If they are already identical → nothing to do, return s.
//  3. Meta on either side → occur-check, then bind and propagate via Eliminate.
//  4. Fun / Fun with the same head and arity → recurse on each argument pair.
//  5. Any other combination (different heads, different arities, Var, …) → Failure.
func robinsonUnify(term1, term2 AST.Term, s Unif.Substitutions) Unif.Substitutions {
	term1 = walkSubst(term1, s)
	term2 = walkSubst(term2, s)

	if term1.Equals(term2) {
		return s
	}

	switch t1 := term1.(type) {
	case AST.Meta:
		if !OccurCheckValid(t1, term2) {
			return Unif.Failure()
		}
		s.Set(t1, term2)
		Unif.EliminateMeta(&s)
		Unif.Eliminate(&s)
		return s

	case AST.Fun:
		switch t2 := term2.(type) {
		case AST.Meta:
			if !OccurCheckValid(t2, term1) {
				return Unif.Failure()
			}
			s.Set(t2, term1)
			Unif.EliminateMeta(&s)
			Unif.Eliminate(&s)
			return s

		case AST.Fun:
			if !t1.GetID().Equals(t2.GetID()) {
				return Unif.Failure()
			}
			args1 := t1.GetArgs().GetSlice()
			args2 := t2.GetArgs().GetSlice()
			if len(args1) != len(args2) {
				return Unif.Failure()
			}
			for i := range args1 {
				s = robinsonUnify(args1[i].Copy(), args2[i].Copy(), s)
				if s.Equals(Failure()) {
					return Unif.Failure()
				}
			}
			return s

		default:
			return Unif.Failure()
		}

	default:
		// Var or any other term kind: not expected after Skolemisation.
		return Unif.Failure()
	}
}

// walkSubst chases meta-variable bindings in s until reaching an unbound
// meta or a non-meta term.
func walkSubst(t AST.Term, s Unif.Substitutions) AST.Term {
	for t.IsMeta() {
		val, idx := s.Get(t.ToMeta())
		if idx == -1 {
			break
		}
		t = val
	}
	return t
}

func EqStructCreate(CCstruct *CCEqualityStruct, tree_pos Unif.DataStructure, atomic Lib.List[AST.Form]) *CCEqualityStruct {

	for _, a := range atomic.GetSlice() {
		sub := a.GetSubTerms().GetSlice()

		for _, t := range sub {

			CCstruct.AddTerm(t)
			//debug(Lib.MkLazy(func() string { return fmt.Sprintf("Atomics: %s", t.ToString()) }))
		}
	}
	//debug(Lib.MkLazy(func() string { return CCstruct.ToString() }))
	CCstruct = addEqualityVar(CCstruct, atomic, tree_pos)

	for CCstruct.congruence() {
	}

	return CCstruct

}

func testInequality(ineq Lib.List[eqStruct.TermPair], CCstruct *CCEqualityStruct) bool {

	testineq := false
	for _, a := range ineq.GetSlice() {

		testineq = CCstruct.testSameparent(CCstruct.retrieveEqTerm(a.GetT1()), CCstruct.retrieveEqTerm(a.GetT2()))
		if testineq {
			break
		}
	}
	return testineq
}

func changeAtomic(atomic Lib.List[AST.Form]) Lib.List[AST.Form] {
	atomicremake := atomic
	atomicConst := Lib.List[AST.Term]{}
	atomicMeta := Lib.List[AST.Term]{}
	for _, a := range atomic.GetSlice() {
		sub := a.GetSubTerms().GetSlice()

		for _, t := range sub {
			if t.GetMetaList().Empty() {
				atomicConst.Append(t)
			} else {
				atomicMeta.Append(t)
			}
		}
	}

	for _, a := range atomic.GetSlice() {
		switch t := a.(type) {
		case AST.Pred:
			if !t.GetMetaList().Empty() {

				for _, b := range t.GetMetaList().GetSlice() {

					for _, c := range atomicConst.GetSlice() {
						replacement := t.Copy()
						replacement = replacement.ReplaceMetaByTerm(b, c)
						atomicremake.Append(replacement)
					}

				}

			}

		case AST.Not:

			switch v := t.GetForm().(type) {
			case AST.Pred:

				if !v.GetMetaList().Empty() {

					for _, b := range v.GetMetaList().GetSlice() {

						for _, c := range atomicConst.GetSlice() {
							replacement := v.Copy()
							replacement = replacement.ReplaceMetaByTerm(b, c)
							atomicremake.Append(replacement)
						}

					}

				}

			}

		default:
		}
	}

	return atomicremake

}

func addEqualityVar(CCstruct *CCEqualityStruct, atomic Lib.List[AST.Form], tree_pos Unif.DataStructure) *CCEqualityStruct {
	eq := retrieveEqualities(tree_pos.Copy())
	atomicConst := Lib.List[AST.Term]{}

	for _, a := range atomic.GetSlice() {
		sub := a.GetSubTerms().GetSlice()

		for _, t := range sub {
			if t.GetMetaList().Empty() {
				atomicConst.Append(t)

			}
		}
	}

	for _, b := range eq {

		e1 := b.GetT1()
		e2 := b.GetT2()
		CCstruct.union(CCstruct.retrieveEqTerm(b.GetT1()), CCstruct.retrieveEqTerm(b.GetT2()))
		if !(e1.GetMetaList().Empty() && e2.GetMetaList().Empty()) {

			if e1.GetMetaList().Len() < e2.GetMetaList().Len() {
				e1, e2 = e2, e1
			}

			generate(atomicConst.GetSlice(), e1.GetMetaList().Len(), func(comb []AST.Term) {

				subste1 := e1.Copy()
				subste2 := e2.Copy()

				for i, v := range e1.GetMetaList().GetSlice() {
					subste1 = subste1.ReplaceSubTermBy(v, comb[i])
					subste2 = subste2.ReplaceSubTermBy(v, comb[i])
				}
				t1, _ := CCstruct.AddTerm(subste1)
				t2, _ := CCstruct.AddTerm(subste2)
				if t1 == nil {
					t1 = CCstruct.retrieveEqTerm(subste1)
				}
				if t2 == nil {
					t2 = CCstruct.retrieveEqTerm(subste2)
				}
				CCstruct.union(t1, t2)
			})

		}

	}

	return CCstruct
}

func allSubstitutions(atomic Lib.List[AST.Form]) []Unif.Substitutions {
	substitutionslist := []Unif.Substitutions{}

	atomicConst := Lib.List[AST.Term]{}
	atomicMeta := Lib.List[AST.Meta]{}

	cmpFunc := func(x, y AST.Term) bool {
		return x.Equals(y)
	}
	cmpMeta := func(x, y AST.Meta) bool {
		return x.Equals(y)
	}
	for _, a := range atomic.GetSlice() {
		sub := a.GetSubTerms().GetSlice()

		for _, t := range sub {
			if t.GetMetaList().Empty() {
				atomicConst.Add(cmpFunc, t)

			} else {
				for _, v := range t.GetMetaList().GetSlice() {
					atomicMeta.Add(cmpMeta, v)

				}
			}
		}
	}
	//debug(Lib.MkLazy(func() string { return fmt.Sprintf("Atomics: %v", Lib.ListToString(atomicConst)) }))
	//debug(Lib.MkLazy(func() string { return fmt.Sprintf("Atomics: %v", Lib.ListToString(atomicMeta)) }))
	generate(atomicConst.GetSlice(), atomicMeta.Len(), func(comb []AST.Term) {
		substitutions := Unif.Substitutions{}
		for i, v := range atomicMeta.GetSlice() {
			subst := Unif.MakeSubstitution(v, comb[i])
			substitutions = append(substitutions, subst)

		}
		//debug(Lib.MkLazy(func() string { return fmt.Sprintf("Sub: %v", substitutions.ToString()) }))
		substitutionslist = Unif.AddSubstToSubstitutionsList(substitutionslist, substitutions)
	})

	return substitutionslist
}

func generate(constants []AST.Term, n int, f func([]AST.Term)) {

	k := len(constants)
	indices := make([]int, n)

	for {
		comb := make([]AST.Term, n)

		for i, v := range indices {
			comb[i] = constants[v]

		}
		f(comb)
		pos := n - 1
		for pos >= 0 {
			indices[pos]++
			if indices[pos] < k {
				break
			}
			indices[pos] = 0
			pos--
		}
		if pos < 0 {
			break
		}
	}
}

func newAtomics(CCstruct *CCEqualityStruct, atomic Lib.List[AST.Form]) (Lib.List[AST.Form], Lib.List[eqStruct.TermPair]) {

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

				if v.GetID().Equals(AST.Id_eq) {
					pairneq.Append(eqStruct.MakeTermPair(v.GetArgs().GetSlice()[0], v.GetArgs().GetSlice()[1]))
				}
			}

		default:

		}
	}
	return atomicsn2, pairneq
}

func trySubtitution(CCstruct *CCEqualityStruct, atomic Lib.List[AST.Form], substitutions Unif.Substitutions) (Lib.List[AST.Form], bool) {
	atomicv8 := Core.ApplySubstitutionsOnFormulaList(Unif.FromSubstitutions(substitutions), Lib.ListCpy(atomic))
	tpa := Unif.NewNode()
	tree_pos := tpa.MakeDataStruct(atomicv8, true)

	CCstruct = EqStructCreate(CCstruct, tree_pos, atomicv8)
	for CCstruct.UpdateParent() {
	}

	atomicv2, ineq := newAtomics(CCstruct, atomicv8)

	//debug(Lib.MkLazy(func() string { return fmt.Sprintf("New atomics : : %v", Lib.ListToString(atomic2)) }))

	if testInequality(ineq, CCstruct) {
		return atomicv2, true
	}

	tna := Unif.NewNode()
	tn := tna.MakeDataStruct(atomicv2, false)

	for _, i := range atomicv2.GetSlice() {
		b, _ := tn.Unify(i)
		if b {

			return atomicv2, true

		}
	}
	return atomicv2, false
}

/**
* Function EqualityReasoning
* Takes atomics
* creates the problem
* returns a bool for success and the corresponding substitution
**/
func EqualityReasoning(CCstruct *CCEqualityStruct, tree_pos, tree_neg Unif.DataStructure, atomic Lib.List[AST.Form], originalNodeId int) (bool, []Unif.Substitutions) {
	debug(Lib.MkLazy(func() string { return "Welcome to the CC module ! ! ! " }))
	debug(Lib.MkLazy(func() string { return fmt.Sprintf("Atomics: %v", Lib.ListToString(atomic)) }))

	substValid := []Unif.Substitutions{}
	subsposible := allSubstitutions(atomic)

	//	debug(Lib.MkLazy(func() string { return CCstruct.ToString() }))
	for _, a := range subsposible {

		CCstruct.Reset()
		atomicv5, val := trySubtitution(CCstruct, atomic, a)

		if val {
			debug(Lib.MkLazy(func() string { return fmt.Sprintf("Atomic Val: %v", Lib.ListToString(atomicv5)) }))
			substValid = append(substValid, a)
			break
		}
	}

	debug(Lib.MkLazy(func() string { return fmt.Sprintf("Substi: %v", len(substValid)) }))
	for _, a := range substValid {
		debug(Lib.MkLazy(func() string { return fmt.Sprintf("Substi: %v", a.ToString()) }))
	}

	//debug(Lib.MkLazy(func() string { return fmt.Sprintf("New atomics : : %v", art[3].ToString()) }))

	if len(substValid) < 1 {
		return false, []Unif.Substitutions{}
	} else {
		return true, substValid
	}

}
