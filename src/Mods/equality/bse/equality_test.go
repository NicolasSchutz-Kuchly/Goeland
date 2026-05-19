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
* This file contains the tests on equality.
**/

package bse

import (
	"fmt"
	"os"
	"testing"
	"time"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Mods/equality/eqStruct"
	"github.com/GoelandProver/Goeland/Typing"
	"github.com/GoelandProver/Goeland/Unif"
)

// Code trees
var tp, tn Unif.DataStructure

// Id
var p_id AST.Id
var g_id AST.Id
var f_id AST.Id
var a_id AST.Id
var b_id AST.Id
var c_id AST.Id
var d_id AST.Id
var c1_id AST.Id
var c2_id AST.Id

// Meta
var x AST.Meta
var y AST.Meta
var z AST.Meta
var z1 AST.Meta
var z2 AST.Meta
var z3 AST.Meta

// Const
var a AST.Fun
var b AST.Fun
var c AST.Fun
var d AST.Fun
var c1 AST.Fun
var c2 AST.Fun

// Fun
var gx AST.Fun
var ga AST.Fun
var fx AST.Fun
var fy AST.Fun
var fa AST.Fun
var fb AST.Fun
var fc AST.Fun

var ggx AST.Fun
var gga AST.Fun
var gfy AST.Fun
var gfa AST.Fun
var fxy AST.Fun
var fyz AST.Fun
var ffx AST.Fun
var fxa AST.Fun
var fay AST.Fun
var fab AST.Fun
var fbc AST.Fun
var fcd AST.Fun

var gggx AST.Fun

var f_fxy_z AST.Fun
var f_x_fyz AST.Fun
var f_fab_c AST.Fun
var f_a_fbc AST.Fun

// Equalities
var eq_x_y AST.Pred
var eq_x_a AST.Pred
var eq_y_a AST.Pred
var eq_z1_c1 AST.Pred
var eq_z1_c2 AST.Pred
var eq_z2_c1 AST.Pred
var eq_z3_c1 AST.Pred
var eq_gx_fx AST.Pred
var eq_ggx_fa AST.Pred
var eq_gfy_y AST.Pred
var eq_fa_a AST.Pred
var eq_b_c AST.Pred
var eq_a_b AST.Pred
var eq_a_c AST.Pred
var eq_b_d AST.Pred
var eq_x_d AST.Pred

// Inequalites
var neq_x_a AST.Form
var neq_a_b AST.Form
var neq_a_d AST.Form
var neq_gggx_x AST.Form
var neq_fx_a AST.Form
var neq_fx_x AST.Form
var neq_fab_fcd AST.Form
var neq_fb_fc AST.Form

// Form
var pggab AST.Form
var pac AST.Form
var pa AST.Form
var pb AST.Form
var not_pc AST.Form
var pab AST.Form
var pax AST.Form
var not_pcd AST.Form

func initTestVariable() {
	// Id
	p_id = AST.MakerId("P")
	g_id = AST.MakerId("g")
	f_id = AST.MakerId("f")
	a_id = AST.MakerId("a")
	b_id = AST.MakerId("b")
	c_id = AST.MakerId("c")
	d_id = AST.MakerId("d")
	c1_id = AST.MakerId("c1")
	c2_id = AST.MakerId("c2")

	// Meta
	x = AST.MakerMeta("X", -1, AST.TIndividual())
	y = AST.MakerMeta("Y", -1, AST.TIndividual())
	z = AST.MakerMeta("Z", -1, AST.TIndividual())
	z1 = AST.MakerMeta("Z1", -1, AST.TIndividual())
	z2 = AST.MakerMeta("Z2", -1, AST.TIndividual())
	z3 = AST.MakerMeta("Z3", -1, AST.TIndividual())

	// Const
	a = AST.MakerConst(a_id)
	b = AST.MakerConst(b_id)
	c = AST.MakerConst(c_id)
	d = AST.MakerConst(d_id)
	c1 = AST.MakerConst(c1_id)
	c2 = AST.MakerConst(c2_id)

	// Fun
	gx = AST.MakerFun(g_id, Lib.MkListV(x.GetTy()), Lib.MkListV[AST.Term](x))
	ga = AST.MakerFun(g_id, a.GetTyArgs(), Lib.MkListV[AST.Term](a))
	fx = AST.MakerFun(f_id, Lib.MkListV(x.GetTy()), Lib.MkListV[AST.Term](x))
	fy = AST.MakerFun(f_id, Lib.MkListV(y.GetTy()), Lib.MkListV[AST.Term](y))
	fa = AST.MakerFun(f_id, a.GetTyArgs(), Lib.MkListV[AST.Term](a))
	fb = AST.MakerFun(f_id, b.GetTyArgs(), Lib.MkListV[AST.Term](b))
	fc = AST.MakerFun(f_id, c.GetTyArgs(), Lib.MkListV[AST.Term](c))

	ggx = AST.MakerFun(g_id, gx.GetTyArgs(), Lib.MkListV[AST.Term](gx))
	gga = AST.MakerFun(g_id, ga.GetTyArgs(), Lib.MkListV[AST.Term](ga))
	gfy = AST.MakerFun(g_id, fy.GetTyArgs(), Lib.MkListV[AST.Term](fy))
	gfa = AST.MakerFun(g_id, fa.GetTyArgs(), Lib.MkListV[AST.Term](fa))
	fxy = AST.MakerFun(f_id, Lib.MkListV(x.GetTy(), y.GetTy()), Lib.MkListV[AST.Term](x, y))
	fyz = AST.MakerFun(f_id, Lib.MkListV(x.GetTy(), z.GetTy()), Lib.MkListV[AST.Term](x, z))
	ffx = AST.MakerFun(f_id, fx.GetTyArgs(), Lib.MkListV[AST.Term](fx))

	x_a_type_list := Lib.MkListV[AST.Ty](x.GetTy())
	x_a_type_list.Append(a.GetTyArgs().GetSlice()...)
	fxa = AST.MakerFun(f_id, x_a_type_list, Lib.MkListV[AST.Term](x, a))

	a_y_type_list := a.GetTyArgs()
	a_y_type_list.Append(y.GetTy())
	fay = AST.MakerFun(f_id, a_y_type_list, Lib.MkListV[AST.Term](a, y))

	a_b_type_list := a.GetTyArgs()
	a_b_type_list.Append(b.GetTyArgs().GetSlice()...)
	fab = AST.MakerFun(f_id, a_b_type_list, Lib.MkListV[AST.Term](a, b))

	bc_type_list := b.GetTyArgs()
	bc_type_list.Append(c.GetTyArgs().GetSlice()...)
	fbc = AST.MakerFun(f_id, bc_type_list, Lib.MkListV[AST.Term](b, c))

	cd_type_list := c.GetTyArgs()
	cd_type_list.Append(d.GetTyArgs().GetSlice()...)
	fcd = AST.MakerFun(f_id, cd_type_list, Lib.MkListV[AST.Term](c, d))

	gggx = AST.MakerFun(g_id, ggx.GetTyArgs(), Lib.MkListV[AST.Term](ggx))

	fxy_z_type_list := fxy.GetTyArgs()
	fxy_z_type_list.Append(z.GetTy())
	f_fxy_z = AST.MakerFun(f_id, fxy_z_type_list, Lib.MkListV[AST.Term](fxy, z))

	x_fyz_type_list := Lib.MkListV[AST.Ty](x.GetTy())
	x_fyz_type_list.Append(fyz.GetTyArgs().GetSlice()...)
	f_x_fyz = AST.MakerFun(f_id, x_fyz_type_list, Lib.MkListV[AST.Term](x, fyz))

	fab_c_type_list := fab.GetTyArgs()
	fab_c_type_list.Append(c.GetTyArgs().GetSlice()...)
	f_fab_c = AST.MakerFun(f_id, fab_c_type_list, Lib.MkListV[AST.Term](fab, c))

	a_fbc_type_list := a.GetTyArgs()
	a_fbc_type_list.Append(fbc.GetTyArgs().GetSlice()...)
	f_a_fbc = AST.MakerFun(f_id, a_fbc_type_list, Lib.MkListV[AST.Term](a, fbc))

	// Equalities
	eq_x_y = AST.MakerPred(AST.Id_eq, Lib.MkListV(x.GetTy(), y.GetTy()), Lib.MkListV[AST.Term](x, y))
	eq_x_a = AST.MakerPred(AST.Id_eq, x_a_type_list, Lib.MkListV[AST.Term](x, a))

	y_a_type_list := Lib.MkListV[AST.Ty](y.GetTy())
	y_a_type_list.Append(a.GetTyArgs().GetSlice()...)
	eq_y_a = AST.MakerPred(AST.Id_eq, y_a_type_list, Lib.MkListV[AST.Term](y, a))

	z_c1_type_list := Lib.MkListV[AST.Ty](z.GetTy())
	z_c1_type_list.Append(c1.GetTyArgs().GetSlice()...)

	eq_z1_c1 = AST.MakerPred(AST.Id_eq, z_c1_type_list, Lib.MkListV[AST.Term](z, c1))

	z1_c2_type_list := Lib.MkListV[AST.Ty](z1.GetTy())
	z1_c2_type_list.Append(c2.GetTyArgs().GetSlice()...)
	eq_z1_c2 = AST.MakerPred(AST.Id_eq, z1_c2_type_list, Lib.MkListV[AST.Term](z1, c2))

	z2_c1_type_list := Lib.MkListV[AST.Ty](z2.GetTy())
	z2_c1_type_list.Append(c1.GetTyArgs().GetSlice()...)
	eq_z2_c1 = AST.MakerPred(AST.Id_eq, z2_c1_type_list, Lib.MkListV[AST.Term](z2, c1))

	z3_c1_type_list := Lib.MkListV[AST.Ty](z3.GetTy())
	z3_c1_type_list.Append(c1.GetTyArgs().GetSlice()...)
	eq_z3_c1 = AST.MakerPred(AST.Id_eq, z3_c1_type_list, Lib.MkListV[AST.Term](z3, c1))

	ggx_fa_type_list := ggx.GetTyArgs()
	ggx_fa_type_list.Append(fa.GetTyArgs().GetSlice()...)
	eq_ggx_fa = AST.MakerPred(AST.Id_eq, ggx_fa_type_list, Lib.MkListV[AST.Term](ggx, fa))

	gfy_y_type_list := gfy.GetTyArgs()
	gfy_y_type_list.Append(y.GetTy())
	eq_gfy_y = AST.MakerPred(AST.Id_eq, gfy_y_type_list, Lib.MkListV[AST.Term](gfy, y))

	gx_fx_type_list := gx.GetTyArgs()
	gx_fx_type_list.Append(fx.GetTyArgs().GetSlice()...)
	eq_gx_fx = AST.MakerPred(AST.Id_eq, gx_fx_type_list, Lib.MkListV[AST.Term](gx, fx))

	fa_a_type_list := fa.GetTyArgs()
	fa_a_type_list.Append(a.GetTyArgs().GetSlice()...)
	eq_fa_a = AST.MakerPred(AST.Id_eq, fa_a_type_list, Lib.MkListV[AST.Term](fa, a))

	a_b_type_list2 := a.GetTyArgs()
	a_b_type_list2.Append(b.GetTyArgs().GetSlice()...)
	eq_a_b = AST.MakerPred(AST.Id_eq, a_b_type_list2, Lib.MkListV[AST.Term](a, b))

	b_c_type_list := b.GetTyArgs()
	b_c_type_list.Append(c.GetTyArgs().GetSlice()...)
	eq_b_c = AST.MakerPred(AST.Id_eq, b_c_type_list, Lib.MkListV[AST.Term](b, c))

	a_c_type_list := a.GetTyArgs()
	a_c_type_list.Append(c.GetTyArgs().GetSlice()...)
	eq_a_c = AST.MakerPred(AST.Id_eq, a_c_type_list, Lib.MkListV[AST.Term](a, c))

	b_d_type_list := b.GetTyArgs()
	b_d_type_list.Append(d.GetTyArgs().GetSlice()...)
	eq_b_d = AST.MakerPred(AST.Id_eq, b_d_type_list, Lib.MkListV[AST.Term](b, d))

	x_d_type_list := Lib.MkListV[AST.Ty](x.GetTy())
	x_d_type_list.Append(d.GetTyArgs().GetSlice()...)
	eq_x_d = AST.MakerPred(AST.Id_eq, x_d_type_list, Lib.MkListV[AST.Term](x, d))

	// Inequalities
	neq_x_a_type_list := Lib.MkListV[AST.Ty](x.GetTy())
	neq_x_a_type_list.Append(a.GetTyArgs().GetSlice()...)
	neq_x_a = AST.MakerNot(AST.MakerPred(AST.Id_eq, neq_x_a_type_list, Lib.MkListV[AST.Term](x, a)))

	neq_a_b_type_list := a.GetTyArgs()
	neq_a_b_type_list.Append(b.GetTyArgs().GetSlice()...)
	neq_a_b = AST.MakerNot(AST.MakerPred(AST.Id_eq, neq_a_b_type_list, Lib.MkListV[AST.Term](a, b)))

	neq_a_d_type_list := a.GetTyArgs()
	neq_a_d_type_list.Append(d.GetTyArgs().GetSlice()...)
	neq_a_d = AST.MakerNot(AST.MakerPred(AST.Id_eq, neq_a_d_type_list, Lib.MkListV[AST.Term](a, d)))

	neq_gggx_x_type_list := gggx.GetTyArgs()
	neq_gggx_x_type_list.Append(x.GetTy())
	neq_gggx_x = AST.MakerNot(AST.MakerPred(AST.Id_eq, neq_gggx_x_type_list, Lib.MkListV[AST.Term](gggx, x)))

	neq_fx_a_type_list := fx.GetTyArgs()
	neq_fx_a_type_list.Append(a.GetTyArgs().GetSlice()...)
	neq_fx_a = AST.MakerNot(AST.MakerPred(AST.Id_eq, neq_fx_a_type_list, Lib.MkListV[AST.Term](fx, a)))

	neq_fx_x_type_list := fx.GetTyArgs()
	neq_fx_x_type_list.Append(x.GetTy())
	neq_fx_x = AST.MakerNot(AST.MakerPred(AST.Id_eq, neq_fx_x_type_list, Lib.MkListV[AST.Term](fx, x)))

	neq_fab_fcd_type_list := fab.GetTyArgs()
	neq_fab_fcd_type_list.Append(fcd.GetTyArgs().GetSlice()...)
	neq_fab_fcd = AST.MakerNot(AST.MakerPred(AST.Id_eq, neq_fab_fcd_type_list, Lib.MkListV[AST.Term](fab, fcd)))

	neq_fb_fc_type_list := fb.GetTyArgs()
	neq_fb_fc_type_list.Append(fc.GetTyArgs().GetSlice()...)
	neq_fb_fc = AST.MakerNot(AST.MakerPred(AST.Id_eq, neq_fb_fc_type_list, Lib.MkListV[AST.Term](fb, fc)))

	// Predicates
	pggab_type_list := gga.GetTyArgs()
	pggab_type_list.Append(b.GetTyArgs().GetSlice()...)
	pggab = AST.MakerPred(p_id, pggab_type_list, Lib.MkListV[AST.Term](gga, b))

	pac_type_list := a.GetTyArgs()
	pac_type_list.Append(c.GetTyArgs().GetSlice()...)
	pac = AST.MakerNot(AST.MakerPred(p_id, pac_type_list, Lib.MkListV[AST.Term](a, c)))

	pa = AST.MakerPred(p_id, a.GetTyArgs(), Lib.MkListV[AST.Term](a))

	pb = AST.MakerPred(p_id, b.GetTyArgs(), Lib.MkListV[AST.Term](b))

	not_pc = AST.MakerNot(AST.MakerPred(p_id, c.GetTyArgs(), Lib.MkListV[AST.Term](c)))

	pab_type_list := a.GetTyArgs()
	pab_type_list.Append(b.GetTyArgs().GetSlice()...)
	pab = AST.MakerPred(p_id, pab_type_list, Lib.MkListV[AST.Term](a, b))

	pax_type_list := a.GetTyArgs()
	pax_type_list.Append(x.GetTy())
	pax = AST.MakerPred(p_id, pax_type_list, Lib.MkListV[AST.Term](a, x))

	not_pcd_type_list := c.GetTyArgs()
	not_pcd_type_list.Append(d.GetTyArgs().GetSlice()...)
	not_pcd = AST.MakerNot(AST.MakerPred(p_id, not_pcd_type_list, Lib.MkListV[AST.Term](c, d)))
}

func initCodeTreesTests(lf Lib.List[AST.Form]) (Unif.DataStructure, Unif.DataStructure) {
	tp = Unif.NewNode()
	tn = Unif.NewNode()
	tp = tp.MakeDataStruct(lf, true)
	tn = tn.MakeDataStruct(lf, false)
	return tp, tn
}

func initDebuggers() {
	AST.InitDebugger()
	InitDebugger()
	Typing.InitDebugger()
	Unif.InitDebugger()
}

func TestMain(m *testing.M) {
	Glob.SetStart(time.Now())
	initDebuggers()
	AST.Init()
	Typing.Init()
	initTestVariable()
	Glob.EnableDebug()
	code := m.Run()
	os.Exit(code)
}

/* Test apply substitution */

func TestAS(t *testing.T) {
	/**
	* Problème : <[X = Y], X, Y>
	* Substitution : (Y, a)
	**/

	// Original problem
	lf := Lib.MkListV[AST.Form](eq_x_y)
	tp, tn = initCodeTreesTests(lf)
	eq := retrieveEqualities(tp.Copy())
	ep := makeEqualityProblem(eq, x, y, makeEmptyConstraintStruct())

	// Expected problem
	lf2 := Lib.MkListV[AST.Form](eq_x_a)
	tp, tn = initCodeTreesTests(lf2)
	eq2 := retrieveEqualities(tp.Copy())
	expected_ep := makeEqualityProblem(eq2, x, a, makeEmptyConstraintStruct())

	s := Unif.MakeEmptySubstitution()
	s.Set(y, a)
	new_ep := ep.applySubstitution(s)

	debug(
		Lib.MkLazy(func() string { return fmt.Sprintf("Current EP : %v", new_ep.ToString()) }),
	)

	debug(
		Lib.MkLazy(func() string { return fmt.Sprintf("Expected : %v", expected_ep.ToString()) }),
	)
}

/*** Test constraints ***/
func TestConstraints1(t *testing.T) {
	/* Not consistent */
	tp_ffx_x := eqStruct.MakeTermPair(ffx, x)
	constraint_ffx_x := MakeConstraint(PREC, tp_ffx_x)
	cs := makeEmptyConstraintStruct()
	append := cs.appendIfConsistent(constraint_ffx_x)

	if append || len(cs.getPrec()) > 0 {
		t.Fatalf("Error: %v and %v is not the expected PREC list. Expected not consistent and empty PREC list", append, cs.getPrec().toString())
	}
}

func TestConstraints2(t *testing.T) {
	/* Consistent but useless */
	tp_x_ffx := eqStruct.MakeTermPair(x, ffx)
	constraint_x_ffx := MakeConstraint(PREC, tp_x_ffx)
	cs := makeEmptyConstraintStruct()
	append := cs.appendIfConsistent(constraint_x_ffx)

	if !append || len(cs.getPrec()) > 0 {
		t.Fatalf("Error: %v and %v is not the expected PREC list. Expected consistent and empty PREC list", append, cs.getPrec().toString())
	}
}

func TestConstraints3(t *testing.T) {
	/* Consistent and relevant */

	tp_x_ffx := eqStruct.MakeTermPair(ffx, fx)
	constraint_fx_a := MakeConstraint(PREC, tp_x_ffx)
	cs := makeEmptyConstraintStruct()
	append := cs.appendIfConsistent(constraint_fx_a)

	t.Fatalf("Error:%v / %v / %v ", append, cs.getPrec().toString(), constraint_fx_a.toString())

}

func TestConstraints4(t *testing.T) {
	/* First constraint is consistent, second is not consistent with the first one */
	/*
	* On accepte les cas comme f(f(x)) < a et a < f(x)
	 */

	tp_fx_a := eqStruct.MakeTermPair(fx, a)
	constraint_fx_a := MakeConstraint(PREC, tp_fx_a)
	cs := makeEmptyConstraintStruct()

	res_constraint_1 := cs.appendIfConsistent(constraint_fx_a)
	if !res_constraint_1 || len(cs.getPrec()) != 1 || !cs.getPrec()[0].equals(constraint_fx_a) {
		t.Fatalf("Error: %v and %v is not the expected PREC list. Expected consistent and %v", res_constraint_1, cs.getPrec().toString(), constraint_fx_a.toString())
	}

	tp_a_fx := eqStruct.MakeTermPair(a, fx)
	constraint_a_fx := MakeConstraint(PREC, tp_a_fx)
	res_constraint_2 := cs.appendIfConsistent(constraint_a_fx)
	if res_constraint_2 || len(cs.getPrec()) != 1 || !cs.getPrec()[0].equals(constraint_fx_a) {
		t.Fatalf("Error: %v and %v is not the expected PREC list. Expected not consistent and %v", res_constraint_2, cs.getPrec().toString(), constraint_fx_a.toString())
	}

}

func TestConstraints5(t *testing.T) {
	cs := makeEmptyConstraintStruct()

	/* Not consistent */
	tp_ffabc_fafbc := eqStruct.MakeTermPair(f_fab_c, f_a_fbc)
	constraint_ffabc_fafbc := MakeConstraint(PREC, tp_ffabc_fafbc)
	res_constraint_1 := cs.appendIfConsistent(constraint_ffabc_fafbc)
	if res_constraint_1 || len(cs.getPrec()) > 0 {
		t.Fatalf("Error: %v and %v is not the expected PREC list. Expected not consistent and empty PREC list", res_constraint_1, cs.getPrec().toString())
	}

	/* Consistent but not relevant */
	tp_fafbc_ffabc := eqStruct.MakeTermPair(f_a_fbc, f_fab_c)
	constraint_fafbc_ffabc := MakeConstraint(PREC, tp_fafbc_ffabc)
	res_constraint_2 := cs.appendIfConsistent(constraint_fafbc_ffabc)
	if !res_constraint_2 || len(cs.getPrec()) > 0 {
		t.Fatalf("Error: %v and %v is not the expected PREC list. Expected consistent and empty PREC list", res_constraint_1, cs.getPrec().toString())
	}
}

func TestConstaintes6(t *testing.T) {
	cs := makeEmptyConstraintStruct()

	/* consistent but not relevant */
	tp_fxfyz_ffxyz := eqStruct.MakeTermPair(f_x_fyz, f_fxy_z)
	constraint_fafbc_ffabc := MakeConstraint(PREC, tp_fxfyz_ffxyz)
	append := cs.appendIfConsistent(constraint_fafbc_ffabc)
	if !append || len(cs.getPrec()) > 0 {
		t.Fatalf("Error: %v and %v is not the expected PREC list. Expected consistent and empty PREC list", append, cs.getPrec().toString())
	}
}

func TestConstaintes7(t *testing.T) {
	cs := makeEmptyConstraintStruct()

	/* consistent, should return X,a and Y, b */
	tp_fxy_fab := eqStruct.MakeTermPair(fxy, fab)
	constraint_fxy_fab := MakeConstraint(EQ, tp_fxy_fab)
	// append :=
	cs.appendIfConsistent(constraint_fxy_fab)
	/*
		if !append || len(cs.getPrec()) > 0 {
			t.Fatalf("Error: %v and %v is not the expected PREC list. Expected consistent and empty PREC list", append, cs.getPrec().toString())
		}
	*/
}

func TestConstaintes8(t *testing.T) {
	cs := makeEmptyConstraintStruct()

	/* consistent, should return X,a and Y, b */
	tp_fxa_fay := eqStruct.MakeTermPair(fxa, fay)
	constraint_fxa_fay := MakeConstraint(EQ, tp_fxa_fay)
	// append :=
	cs.appendIfConsistent(constraint_fxa_fay)
	/*
		if !append || len(cs.getPrec()) > 0 {
			t.Fatalf("Error: %v and %v is not the expected PREC list. Expected consistent and empty PREC list", append, cs.getPrec().toString())
		}
	*/
}

func TestConstaintes9(t *testing.T) {
	cs := makeEmptyConstraintStruct()

	/* consistent, should return X,a and Y, b */
	tp_gga_ggx := eqStruct.MakeTermPair(gga, ggx)
	constraint_gga_ggx := MakeConstraint(PREC, tp_gga_ggx)
	// append :=
	cs.appendIfConsistent(constraint_gga_ggx)
	/*
		if !append || len(cs.getPrec()) > 0 {
			t.Fatalf("Error: %v and %v is not the expected PREC list. Expected consistent and empty PREC list", append, cs.getPrec().toString())
		}
	*/
}

// ---------------------------------------------------------------------------
// LPO / PREC edge cases
// ---------------------------------------------------------------------------

// Two identical deferred constraints: the second must be accepted (idempotent).
// f(X) ≺ a  added twice → still only one entry in prec list.
func TestConstraints_Idempotent(t *testing.T) {
	tp_fx_a := eqStruct.MakeTermPair(fx, a)
	c := MakeConstraint(PREC, tp_fx_a)
	cs := makeEmptyConstraintStruct()

	res1 := cs.appendIfConsistent(c)
	res2 := cs.appendIfConsistent(c) // duplicate

	if !res1 || !res2 {
		t.Fatalf("Both insertions should return true for a duplicate, got %v %v", res1, res2)
	}
	if len(cs.getPrec()) != 1 {
		t.Fatalf("Duplicate constraint should not grow the prec list; got %v", cs.getPrec().toString())
	}
}

// Two distinct deferred constraints that are compatible: both must be accepted.
// f(X) ≺ a  and  g(Y) ≺ b  — different metas, no conflict.
func TestConstraints_TwoCompatibleDeferred(t *testing.T) {
	c1 := MakeConstraint(PREC, eqStruct.MakeTermPair(fx, a))
	c2 := MakeConstraint(PREC, eqStruct.MakeTermPair(fy, b))
	cs := makeEmptyConstraintStruct()

	if !cs.appendIfConsistent(c1) {
		t.Fatalf("c1 should be consistent")
	}
	if !cs.appendIfConsistent(c2) {
		t.Fatalf("c2 should be consistent with c1")
	}
	if len(cs.getPrec()) != 2 {
		t.Fatalf("Expected 2 deferred constraints, got %v", cs.getPrec().toString())
	}
}

// g(g(g(X))) ≺ X is an occur-check violation in LPO (X appears inside gggx).
// Must be rejected.
func TestConstraints_OccurCheckPREC(t *testing.T) {
	tp := eqStruct.MakeTermPair(gggx, x)
	c := MakeConstraint(PREC, tp)
	cs := makeEmptyConstraintStruct()

	if cs.appendIfConsistent(c) {
		t.Fatalf("ggg(X) ≺ X should be rejected (occur-check)")
	}
}

// Ground PREC that is trivially satisfied and does not interact with any
// deferred constraint: a ≺ f(a). Pure ground, f > a, no metas.
// Expected: consistent, not added to prec list (ground/comparable).
func TestConstraints_GroundSatisfied(t *testing.T) {
	tp := eqStruct.MakeTermPair(a, fa)
	c := MakeConstraint(PREC, tp)
	cs := makeEmptyConstraintStruct()

	if !cs.appendIfConsistent(c) {
		t.Fatalf("a ≺ f(a) should be consistent (ground, f>a)")
	}
	if len(cs.getPrec()) != 0 {
		t.Fatalf("Ground comparable constraint should not be deferred; prec=%v", cs.getPrec().toString())
	}
}

// Ground PREC that is violated: f(a) ≺ a. f > a, so f(a) > a in LPO.
// Expected: rejected.
func TestConstraints_GroundViolated(t *testing.T) {
	tp := eqStruct.MakeTermPair(fa, a)
	c := MakeConstraint(PREC, tp)
	cs := makeEmptyConstraintStruct()

	if cs.appendIfConsistent(c) {
		t.Fatalf("f(a) ≺ a should be rejected (ground, f>a so f(a)>a)")
	}
}

// Three-way cycle: X ≺ f(X) is fine, but then adding f(X) ≺ X must fail.
func TestConstraints_Cycle(t *testing.T) {
	c_x_fx := MakeConstraint(PREC, eqStruct.MakeTermPair(x, fx))
	c_fx_x := MakeConstraint(PREC, eqStruct.MakeTermPair(fx, x))
	cs := makeEmptyConstraintStruct()

	// X ≺ f(X): X occurs inside f(X), so this is detected as comparable and
	// satisfied (occur-check direction), prec list stays empty.
	if !cs.appendIfConsistent(c_x_fx) {
		t.Fatalf("X ≺ f(X) should be consistent")
	}
	// f(X) ≺ X: occur-check in reverse → must be rejected.
	if cs.appendIfConsistent(c_fx_x) {
		t.Fatalf("f(X) ≺ X should be rejected after X ≺ f(X)")
	}
}

// ---------------------------------------------------------------------------
// EQ edge cases
// ---------------------------------------------------------------------------

// EQ constraint with already-equal ground terms: a ≃ a → trivially consistent.
func TestConstraintsEQ_SameTerm(t *testing.T) {
	c := MakeConstraint(EQ, eqStruct.MakeTermPair(a, a))
	cs := makeEmptyConstraintStruct()

	if !cs.appendIfConsistent(c) {
		t.Fatalf("a ≃ a should be consistent")
	}
}

// EQ constraint between two distinct ground constants: a ≃ b → not unifiable.
func TestConstraintsEQ_GroundConflict(t *testing.T) {
	c := MakeConstraint(EQ, eqStruct.MakeTermPair(a, b))
	cs := makeEmptyConstraintStruct()

	if cs.appendIfConsistent(c) {
		t.Fatalf("a ≃ b should be rejected (a ≠ b ground)")
	}
}

// EQ constraint X ≃ a followed by a PREC constraint f(X) ≺ a.
// After substituting X→a, f(X) becomes f(a), and f(a) ≺ a is ground-violated.
// Expected: the PREC is rejected.
func TestConstraints_EQThenPREC_Conflict(t *testing.T) {
	cs := makeEmptyConstraintStruct()

	cEQ := MakeConstraint(EQ, eqStruct.MakeTermPair(x, a))
	if !cs.appendIfConsistent(cEQ) {
		t.Fatalf("X ≃ a should be accepted")
	}

	cPREC := MakeConstraint(PREC, eqStruct.MakeTermPair(fx, a))
	if cs.appendIfConsistent(cPREC) {
		t.Fatalf("f(X) ≺ a with X→a means f(a) ≺ a, which is violated — should be rejected")
	}
}

// EQ constraint X ≃ a followed by a PREC constraint a ≺ f(X).
// After substituting X→a, a ≺ f(a) is ground-satisfied.
// Expected: the PREC is accepted.
func TestConstraints_EQThenPREC_Satisfied(t *testing.T) {
	cs := makeEmptyConstraintStruct()

	cEQ := MakeConstraint(EQ, eqStruct.MakeTermPair(x, a))
	if !cs.appendIfConsistent(cEQ) {
		t.Fatalf("X ≃ a should be accepted")
	}

	cPREC := MakeConstraint(PREC, eqStruct.MakeTermPair(a, fx))
	if !cs.appendIfConsistent(cPREC) {
		t.Fatalf("a ≺ f(X) with X→a means a ≺ f(a), which is satisfied — should be accepted")
	}
}

// Deferred PREC f(X) ≺ a, then EQ X ≃ a.
// Applying X→a to the deferred constraint gives f(a) ≺ a — violated.
// The EQ must be rejected because it breaks the stored PREC constraint.
func TestConstraints_PRECThenEQ_Conflict(t *testing.T) {
	cs := makeEmptyConstraintStruct()

	cPREC := MakeConstraint(PREC, eqStruct.MakeTermPair(fx, a))
	if !cs.appendIfConsistent(cPREC) {
		t.Fatalf("f(X) ≺ a should be deferred")
	}

	cEQ := MakeConstraint(EQ, eqStruct.MakeTermPair(x, a))
	if cs.appendIfConsistent(cEQ) {
		t.Fatalf("X ≃ a should be rejected: it instantiates f(X) ≺ a to f(a) ≺ a which is violated")
	}
}

// Two conflicting EQ constraints: X ≃ a then X ≃ b.
// Second should be rejected because the substitution already maps X to a.
func TestConstraintsEQ_ConflictingSubst(t *testing.T) {
	cs := makeEmptyConstraintStruct()

	c1 := MakeConstraint(EQ, eqStruct.MakeTermPair(x, a))
	c2 := MakeConstraint(EQ, eqStruct.MakeTermPair(x, b))

	if !cs.appendIfConsistent(c1) {
		t.Fatalf("X ≃ a should be accepted")
	}
	if cs.appendIfConsistent(c2) {
		t.Fatalf("X ≃ b should be rejected: X is already bound to a")
	}
}

// Two compatible EQ constraints on different metas: X ≃ a then Y ≃ b.
// Both should be accepted and the substitution should contain both bindings.
func TestConstraintsEQ_CompatibleSubst(t *testing.T) {
	cs := makeEmptyConstraintStruct()

	c1 := MakeConstraint(EQ, eqStruct.MakeTermPair(x, a))
	c2 := MakeConstraint(EQ, eqStruct.MakeTermPair(y, b))

	if !cs.appendIfConsistent(c1) {
		t.Fatalf("X ≃ a should be accepted")
	}
	if !cs.appendIfConsistent(c2) {
		t.Fatalf("Y ≃ b should be accepted alongside X ≃ a")
	}

	s := cs.getSubst()
	xBound := false
	yBound := false
	for _, pair := range s {
		m, t := pair.Get()
		if m.Equals(x) && t.Equals(a) {
			xBound = true
		}
		if m.Equals(y) && t.Equals(b) {
			yBound = true
		}
	}
	if !xBound || !yBound {
		t.Fatalf("Expected substitution {X→a, Y→b}, got %v", s.ToString())
	}
}

// Substitution applied to a PREC that remains comparable after instantiation,
// but in the satisfying direction: deferred f(X) ≺ g(a), then X ≃ a.
// After X→a: f(a) ≺ g(a). f < g so f(a) < g(a) in LPO — satisfied.
// Expected: EQ accepted, prec list cleared (constraint resolved).
func TestConstraints_PRECResolvedByEQ(t *testing.T) {
	cs := makeEmptyConstraintStruct()

	// f(X) ≺ g(a): f < g, but X is free → deferred
	cPREC := MakeConstraint(PREC, eqStruct.MakeTermPair(fx, ga))
	if !cs.appendIfConsistent(cPREC) {
		t.Fatalf("f(X) ≺ g(a) should be deferred as consistent")
	}
	if len(cs.getPrec()) != 1 {
		t.Fatalf("f(X) ≺ g(a) should be in the prec list, got %v", cs.getPrec().toString())
	}

	// X ≃ a: should be accepted; after applying, the deferred PREC is satisfied.
	cEQ := MakeConstraint(EQ, eqStruct.MakeTermPair(x, a))
	if !cs.appendIfConsistent(cEQ) {
		t.Fatalf("X ≃ a should be accepted; it resolves f(X) ≺ g(a) to f(a) ≺ g(a) which holds")
	}
}

// Empty constraint struct — isEmpty must hold.
func TestConstraintStruct_Empty(t *testing.T) {
	cs := makeEmptyConstraintStruct()
	if !cs.isEmpty() {
		t.Fatalf("Fresh constraint struct should be empty")
	}
}

// After a successful PREC insertion the struct is no longer empty.
func TestConstraintStruct_NotEmptyAfterInsert(t *testing.T) {
	cs := makeEmptyConstraintStruct()
	c := MakeConstraint(PREC, eqStruct.MakeTermPair(fx, a))
	cs.appendIfConsistent(c)
	if cs.isEmpty() {
		t.Fatalf("Struct should not be empty after inserting a deferred constraint")
	}
}

// copy() must produce a deep copy: mutating the copy must not affect the original.
func TestConstraintStruct_Copy(t *testing.T) {
	cs := makeEmptyConstraintStruct()
	c := MakeConstraint(PREC, eqStruct.MakeTermPair(fx, a))
	cs.appendIfConsistent(c)

	csCopy := cs.copy()

	// Add a new constraint only to the copy.
	c2 := MakeConstraint(PREC, eqStruct.MakeTermPair(fy, b))
	csCopy.appendIfConsistent(c2)

	if len(cs.getPrec()) != 1 {
		t.Fatalf("Original prec list should still have 1 element after mutating the copy; got %v", cs.getPrec().toString())
	}
	if len(csCopy.getPrec()) != 2 {
		t.Fatalf("Copy prec list should have 2 elements; got %v", csCopy.getPrec().toString())
	}
}

// A substitution that maps X to itself (identity) should be treated as empty/trivial.
func TestConstraintsEQ_IdentitySubst(t *testing.T) {
	cs := makeEmptyConstraintStruct()
	s := Unif.MakeEmptySubstitution()
	s.Set(x, x)
	cs.setSubst(s)

	// f(X) ≺ a with a substitution that maps X→X: effectively no change.
	cPREC := MakeConstraint(PREC, eqStruct.MakeTermPair(fx, a))
	if !cs.appendIfConsistent(cPREC) {
		t.Fatalf("f(X) ≺ a should still be deferred as consistent with identity subst")
	}
}
