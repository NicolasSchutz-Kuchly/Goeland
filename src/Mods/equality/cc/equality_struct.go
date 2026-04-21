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
	classes []*Eqterm
}

func newCCEqualityStruct() *CCEqualityStruct {
	return &CCEqualityStruct{}
}

func (cc *CCEqualityStruct) AddTerm(t AST.Term) (*Eqterm, int) {
	if contain := cc.retrieveEqTerm(t); contain != nil {
		return contain, contain.len
	}
	e := NewEqTerm(&t)
	e.setParent(e)
	lenmax := 1
	lenmaj := 1

	if f, ok := t.(AST.Fun); ok {
		for indice, arg := range f.GetArgs().GetSlice() {
			h, k := cc.AddTerm(arg)
			lenmaj = max(1+k, lenmaj)
			e.use[indice] = h
		}
		lenmax = max(lenmax, lenmaj)
	}

	e.setLen(lenmax)
	cc.classes = append(cc.classes, e)
	return e, lenmax

}

func (cc *CCEqualityStruct) ToString() string {
	var b strings.Builder

	b.WriteString("CCEqualityStruct {\n")

	for _, c := range cc.classes {

		b.WriteString(fmt.Sprintf("Term : %s", c.ToString()))

		b.WriteString("\n")
	}
	b.WriteString("}\n")

	return b.String()
}

func (cc *CCEqualityStruct) retrieveEqTerm(term AST.Term) *Eqterm {
	for _, e := range cc.classes {
		if e.term.Equals(term) {
			return e
		}
	}
	return nil
}

func (cc *CCEqualityStruct) createParent(e *Eqterm) bool {
	testchange := len(cc.classes)
	if e.isParent() {
		switch fun := e.term.(type) {
		case AST.Fun:

			args := Lib.List[AST.Term]{}

			for _, v := range fun.GetArgs().GetSlice() {
				args.Append(find(cc.retrieveEqTerm(v)).term)
			}
			newparent := AST.MakeFun(fun.GetP(), Lib.ListCpy(fun.GetTyArgs()), args, fun.GetMetas())
			l, _ := cc.AddTerm(newparent)
			find(e).setParent(l)
		default:
		}
	}
	return testchange != len(cc.classes)
}

func (cc *CCEqualityStruct) UpdateParent() bool {
	loop := false
	for _, e := range cc.classes {
		loop = cc.createParent(e) || loop
	}
	return loop
}

func (cc *CCEqualityStruct) GetParentList() []*Eqterm {
	res := []*Eqterm{}
	for _, e := range cc.classes {
		if e.isParent() {
			res = append(res, e)
		}
	}
	return res
}

func find(e *Eqterm) *Eqterm {
	if e.term.Equals(e.parent.term) {
		return e
	} else {
		return find(e.parent)
	}
}

func (cc *CCEqualityStruct) union(term *Eqterm, term2 *Eqterm) {

	x := term
	y := term2
	if !cc.testSameparent(term, term2) {

		if find(x).len > find(y).len {
			x, y = y, x
		}

		find(y).setParent(find(x))

	}
}

func (cc *CCEqualityStruct) testSameparent(term1 *Eqterm, term2 *Eqterm) bool {
	return find(term1).term.Equals(find(term2).term)
}

func (cc *CCEqualityStruct) congruence() bool {
	res := false
	for _, e := range cc.classes {
		if !(len(e.use) == 0) {
			for _, e2 := range cc.classes {
				if e2.term.GetIndex() == e.term.GetIndex() && find(e) != find(e2) {
					if equalMaps(e2.use, e.use) {
						cc.union(e, e2)
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
	return t.term.Equals(find(t).term)
}

func (t *Eqterm) setLen(p int) {
	t.len = p
}

func (t *Eqterm) ToString() string {
	str := fmt.Sprintf("%v (class: %s)", t.term.ToString(), find(t).term.ToString())
	first := true

	str += fmt.Sprintf(" (len : %d) ", t.len)
	for i := 0; i < len(t.use); i++ {

		if val, ok := t.use[i]; ok {
			if !first {
				str += ", "

			} else {
				str += "( arg :"
			}
			str += fmt.Sprintf("%s", val.term.ToString())
			first = false
		}
	}

	str += ")"
	return str
}

func NewEqTerm(term *AST.Term) *Eqterm {
	return &Eqterm{term: *term,
		use: make(map[int]*Eqterm),
	}
}

func equalMaps(a, b map[int]*Eqterm) bool {
	for k := range a {
		if !(find(a[k]).term.Equals(find(b[k]).term)) {
			return false
		}
	}
	return true
}
