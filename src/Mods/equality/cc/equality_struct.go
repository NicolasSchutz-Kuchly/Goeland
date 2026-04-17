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

func newCCEqualityStruct() *CCEqualityStruct {
	return &CCEqualityStruct{}
}

func (cc *CCEqualityStruct) AddTerm(t AST.Term) bool {
	if contain := cc.retrieveEqTerm(t); contain != nil {
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
	e.setClass(c)
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
			terms = append(terms, fmt.Sprintf(" %s ", e.ToString()))
		}

		b.WriteString(strings.Join(terms, " "))
		b.WriteString("\n")
	}

	b.WriteString("}\n")

	return b.String()
}

func (cc *CCEqualityStruct) retrieveEqTerm(term AST.Term) *Eqterm {
	for _, e := range cc.classes {
		for _, t := range e.terms {
			if t.term.Equals(term) {
				return t
			}
		}
	}
	return nil
}

func (cc *CCEqualityStruct) find(term *Eqterm) *eqClass {
	return term.class
}

func (cc *CCEqualityStruct) union(term *Eqterm, term2 *Eqterm) *eqClass {
	e1 := cc.find(term)
	e2 := cc.find(term2)

	if e1 == nil || e2 == nil || e1 == e2 {
		return nil
	}

	toRemove := e1.union(e2)

	if toRemove != nil {
		cc.removeClass(toRemove)
	}

	return cc.find(term)
}

func (cc *CCEqualityStruct) initArgsEq() {
	for _, e := range cc.classes {
		for _, t := range e.terms {

			if f, ok := t.term.(AST.Fun); ok {
				for indice, arg := range f.GetArgs().GetSlice() {
					t.use[indice] = cc.retrieveEqTerm(arg)

				}
			}
		}
	}
}

func (cc *CCEqualityStruct) testSameclass(term1 *Eqterm, term2 *Eqterm) bool {
	return term1.class == term2.class
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
			if !(len(t.use) == 0) {

				for _, e2 := range cc.classes {
					for _, t2 := range e2.terms {
						if t2.term.GetIndex() == t.term.GetIndex() && cc.find(t) != cc.find(t2) {
							if equalMaps(t2.use, t.use) {
								cc.union(t, t2)
								res = true
							}
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

func (e *eqClass) union(e2 *eqClass) *eqClass {
	x := e
	y := e2

	if x == y {
		return nil
	}

	if x.size < y.size {
		x, y = y, x
	}

	x.terms = append(x.terms, y.terms...)
	for _, e := range y.terms {
		e.setClass(x)
	}
	x.size = len(x.terms)
	return y
}

type Eqterm struct {
	term  AST.Term
	class *eqClass
	use   map[int]*Eqterm
}

func (t *Eqterm) setClass(cl *eqClass) {
	t.class = cl
}

func (t *Eqterm) ToString() string {
	str := t.term.ToString() + fmt.Sprintf("(class: %d)", t.class.id)
	first := true
	for i := 0; i < len(t.use); i++ {
		if val, ok := t.use[i]; ok {
			if !first {
				str += ", "

			} else {
				str += "( arg :"
			}
			str += fmt.Sprintf("%d", val.class.id)
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
		if a[k].class != b[k].class {
			return false
		}
	}
	return true
}
