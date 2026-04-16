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
)

type CCEqualityStruct struct {
	classes []*eqClass
}

func (cc *CCEqualityStruct) propagation(receive *eqClass, deletable *eqClass) {

}

func newCCEqualityStruct() *CCEqualityStruct {
	return &CCEqualityStruct{}
}

func (cc *CCEqualityStruct) AddTerm(t AST.Term) bool {
	if contain := cc.find(t); contain != nil {
		return false
	}

	cc.makeEqClass(t)
	return true
}

func (cc *CCEqualityStruct) makeEqClass(t AST.Term) *eqClass {
	e := NewEqTerm(&t)

	c := &eqClass{
		id:    len(cc.classes),
		terms: []*Eqterm{},
		size:  1,
		resp:  e,
	}

	c.terms = append(c.terms, e)

	cc.classes = append(cc.classes, c)

	return c
}

func (cc *CCEqualityStruct) ToString() string {
	var b strings.Builder

	b.WriteString("CCEqualityStruct {\n")

	for _, c := range cc.classes {
		b.WriteString(fmt.Sprintf("  Class %d: ", c.id))

		var terms []string
		terms = append(terms, fmt.Sprintf("Terms : "))
		for _, e := range c.terms {
			terms = append(terms, fmt.Sprintf(" %s ", e.term.ToString()))
		}

		b.WriteString(strings.Join(terms, " "))
		b.WriteString("\n")
	}

	b.WriteString("}\n")

	return b.String()
}
func (cc *CCEqualityStruct) find(term AST.Term) *eqClass {
	for _, e := range cc.classes {
		if e.Contain(term) {
			return e
		}
	}
	return nil
}

func (cc *CCEqualityStruct) merge(term AST.Term, term2 AST.Term) bool {
	e1 := cc.find(term)
	e2 := cc.find(term2)

	if e1 == nil || e2 == nil || e1 == e2 {
		return false
	}

	toRemove := e1.merge(e2)

	if toRemove != nil {
		cc.removeClass(toRemove)
	}

	return true
}
func (cc *CCEqualityStruct) updateArgsEq() {
	for _, e := range cc.classes {
		for _, t := range e.terms {

			if f, ok := t.term.(AST.Fun); ok {
				for indice, arg := range f.GetArgs().GetSlice() {
					t.use[indice] = cc.find(arg)

				}
			}

		}
	}
}

func (cc *CCEqualityStruct) initArgsEq() {
	for _, e := range cc.classes {
		for _, t := range e.terms {

			if f, ok := t.term.(AST.Fun); ok {
				for indice, arg := range f.GetArgs().GetSlice() {
					t.use[indice] = cc.find(arg)

				}
			}

		}
	}
}

func (cc *CCEqualityStruct) removeClass(target *eqClass) {
	for i, c := range cc.classes {
		if c == target {
			cc.classes = append(cc.classes[:i], cc.classes[i+1:]...)
			return
		}
	}
}

func (cc *CCEqualityStruct) congruence() bool {
	res := false
	for _, e := range cc.classes {
		for _, t := range e.terms {

			for _, e2 := range cc.classes {
				for _, t2 := range e2.terms {
					if t2.term.GetIndex() == t.term.GetIndex() && cc.find(t.term) != cc.find(t2.term) {
						if equalMaps(t2.use, t.use) {
							cc.merge(t.term, t2.term)
							res = true
						}
					}

				}
			}
		}
	}
	return res
}

type eqClass struct {
	id    int
	resp  *Eqterm
	terms []*Eqterm
	size  int
}

func NewEqClass(term *AST.Term) *eqClass {
	return &eqClass{}
}

func (e *eqClass) Contain(a AST.Term) bool {
	for _, t := range e.terms {
		if t.term.Equals(a) {
			return true
		}
	}
	return false
}
func (e *eqClass) ToString() string {
	return fmt.Sprintf("(id: %d)", e.id)
}

func (e *eqClass) Getresp() Eqterm {
	return *e.resp
}

func (e *eqClass) merge(e2 *eqClass) *eqClass {
	x := e
	y := e2

	if x == y {
		return nil
	}

	if x.size < y.size {
		x, y = y, x
	}

	x.terms = append(x.terms, y.terms...)
	x.size = len(x.terms)
	return y
}

type Eqterm struct {
	term AST.Term
	use  map[int]*eqClass
}

func (t *Eqterm) ToString() string {
	str := t.term.ToString() + " ("

	first := true
	for i := 0; i < len(t.use); i++ {
		if val, ok := t.use[i]; ok {
			if !first {
				str += ", "
			}
			str += val.ToString()
			first = false
		}
	}

	str += ")"
	return str
}

func NewEqTerm(term *AST.Term) *Eqterm {
	return &Eqterm{term: *term,
		use: make(map[int]*eqClass),
	}
}

func equalMaps(a, b map[int]*eqClass) bool {
	for k := range a {
		if a[k] != b[k] {
			return false
		}
	}
	return true
}
