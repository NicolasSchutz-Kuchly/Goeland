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
	"github.com/GoelandProver/Goeland/Lib"
)

type CCEqualityStruct struct {
	classes map[int][]*Eqterm
}

func newCCEqualityStruct() CCEqualityStruct {
	return CCEqualityStruct{classes: make(map[int][]*Eqterm)}
}

/*
add a ASTterm in the CCstruct and return the corresponding Eqterm and its depth
add its args in the cc struct too
if the term is already in the CCstruct do nothing
*/
func (cc *CCEqualityStruct) AddTerm(t AST.Term) (*Eqterm, int) {
	if contain := cc.retrieveEqTerm(t); contain != nil {
		return contain, contain.len
	}

	e := NewEqTerm(&t)
	debug(Lib.MkLazy(func() string { return fmt.Sprintf("Add %v in CCstruct", t.ToString()) }))
	e.setParent(e)
	lenmax := 1
	lenmaj := 1

	if f, ok := t.(AST.Fun); ok {
		for indice, arg := range f.GetArgs().GetSlice() {
			term, leng := cc.AddTerm(arg)
			lenmaj = max(1+leng, lenmaj)
			e.use[indice] = term
		}
		lenmax = max(lenmax, lenmaj)
	}

	e.setLen(lenmax)
	index := e.term.GetIndex()
	cc.classes[index] = append(cc.classes[index], e)
	return e, lenmax
}

func (cc CCEqualityStruct) ToString() string {
	var b strings.Builder

	b.WriteString("\nEquality Struct :\n")

	for _, c := range cc.classes {
		for _, d := range c {

			b.WriteString(fmt.Sprintf("	%s", d.ToString()))

			b.WriteString("\n")
		}
	}
	return b.String()
}

/*
return the eqterm corresponding to the astterm , if it's not in the ccstruct , return nil
*/
func (cc *CCEqualityStruct) retrieveEqTerm(term AST.Term) *Eqterm {
	for _, e := range cc.classes[term.GetIndex()] {
		if e.term.Equals(term) {
			return e
		}
	}
	return nil
}

func (cc *CCEqualityStruct) isInStruct(eqterm *Eqterm) bool {
	for _, e := range cc.classes[eqterm.term.GetIndex()] {
		if e.Equals(eqterm) {
			return true
		}
	}
	return false
}

/*
Normalize the parents : if a parent is f(a,b) try to replace a and b by their representative
and create a new parent f(a,a) for example
return a bool to see if the ccstruct is stable or not
*/
func (cc *CCEqualityStruct) createParent(e *Eqterm) bool {
	testExist := true
	switch fun := e.term.(type) {

	case AST.Fun:
		args := Lib.List[AST.Term]{}

		for _, k := range e.use {
			res := find(k)
			if !res.Equals(k) {
				testExist = false
			}
			args.Append(res.term)
			debug(Lib.MkLazy(func() string {
				return fmt.Sprintf("Replace arg %v with %v in %v", k.term.ToString(), res.term.ToString(), e.term.ToString())
			}))
		}

		if !testExist {
			newparent := AST.MakeFun(fun.GetP(), Lib.ListCpy(fun.GetTyArgs()), args, fun.GetMetas())
			l, _ := cc.AddTerm(newparent)
			find(e).setParent(find(l))
			debug(Lib.MkLazy(func() string {
				return fmt.Sprintf("Ajout parent normalisé %v ", newparent.ToString())
			}))
		}
	default:
	}

	return !testExist
}

/*
for all the eqstruct , try to normalise it if its a representative return true if something changed
*/
func (cc *CCEqualityStruct) UpdateParent() bool {
	loop := false
	for _, f := range cc.classes {
		for _, e := range f {
			if e.isParent() && e.len != 0 {
				loop = cc.createParent(e) || loop
			}
		}
	}
	return loop
}

/*
return the parent of an eqterm , compress the path too (each term must be directed connected to their
representative)
*/
func find(e *Eqterm) *Eqterm {

	if e.isParent() {
		return e
	}
	e.parent = find(e.parent)
	return e.parent
}

/*
take 2 term and fuse their eqclass , take the best reprensative between the 2 possibles
*/
func (cc *CCEqualityStruct) union(term *Eqterm, term2 *Eqterm) {

	x := term
	y := term2
	px := find(x)
	py := find(y)

	/*
		pour le choix du parent regarde le nombre d'arguments puis la profondeur
	*/
	if !px.Equals(py) {
		if len(px.use) > len(py.use) {
			px, py = py, px
		} else if px.len > py.len && len(px.use) == len(py.use) {
			px, py = py, px
		}
		py.setParent(px)
		debug(Lib.MkLazy(func() string {
			return fmt.Sprintf("Union %v and %v , new parent : %v", term.term.ToString(), term2.term.ToString(), py.parent.term.ToString())
		}))

	}
}

func (t *Eqterm) Copy() *Eqterm {
	return &Eqterm{
		term: t.term,
		len:  t.len,
		use:  make(map[int]*Eqterm),
	}
}

func (cc *CCEqualityStruct) testSameparent(term1 *Eqterm, term2 *Eqterm) bool {

	return find(term1).Equals(find(term2))
}

func (cc *CCEqualityStruct) congruence() bool {
	res := false
	for _, termlist := range cc.classes {
		if len(termlist) < 2 {
			continue
		}
		for i, e := range termlist {
			if len(e.use) == 0 {
				continue
			}
			for j := i + 1; j < len(termlist); j++ {
				e2 := termlist[j]
				pe2 := find(e2)
				pe := find(e)
				if !pe.Equals(pe2) {
					if equalMaps(e2.use, e.use) {
						cc.union(e, e2)
						debug(Lib.MkLazy(func() string {
							return fmt.Sprintf("Ajout union congruence : %v = %v (Parent : %v)", e.term.ToString(), e2.term.ToString(), pe.term.ToString())
						}))
						res = true
					}
				}
			}
		}
	}
	return res
}

type Eqterm struct {
	term   AST.Term
	parent *Eqterm
	len    int
	use    map[int]*Eqterm
}

func (t *Eqterm) setParent(p *Eqterm) {
	t.parent = p
}

func (t *Eqterm) isParent() bool {
	return t.Equals(t.parent)
}

func (t *Eqterm) setLen(p int) {
	t.len = p
}

func (t *Eqterm) ToString() string {
	str := fmt.Sprintf("	%v (Representative: %s )", t.term.ToString(), find(t).term.ToString())
	return str
}

func NewEqTerm(term *AST.Term) *Eqterm {
	return &Eqterm{term: *term,
		use: make(map[int]*Eqterm),
	}
}

/*
test if parent map1[i] = parent map2[i] for i in len map1
*/
func equalMaps(a, b map[int]*Eqterm) bool {
	if len(a) != len(b) {
		return false
	}

	for i, v := range a {
		if !find(v).Equals(find(b[i])) {
			return false
		}
	}
	return true
}

func (t *Eqterm) Equals(t1 *Eqterm) bool {

	return t.term.Equals(t1.term)
}
