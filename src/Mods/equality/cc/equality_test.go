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

package cc

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
var gb AST.Fun
var fx AST.Fun
var fy AST.Fun
var fa AST.Fun
var fb AST.Fun
var fc AST.Fun

var ggx AST.Fun
var gga AST.Fun
var ggb AST.Fun
var gfy AST.Fun
var gfa AST.Fun
var fxy AST.Fun
var fyz AST.Fun
var ffx AST.Fun
var fxa AST.Fun
var fay AST.Fun
var fab AST.Fun
var faa AST.Fun
var fbb AST.Fun
var fbc AST.Fun
var fac AST.Fun
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
	gb = AST.MakerFun(g_id, b.GetTyArgs(), Lib.MkListV[AST.Term](b))
	fx = AST.MakerFun(f_id, Lib.MkListV(x.GetTy()), Lib.MkListV[AST.Term](x))
	fy = AST.MakerFun(f_id, Lib.MkListV(y.GetTy()), Lib.MkListV[AST.Term](y))
	fa = AST.MakerFun(f_id, a.GetTyArgs(), Lib.MkListV[AST.Term](a))
	fb = AST.MakerFun(f_id, b.GetTyArgs(), Lib.MkListV[AST.Term](b))
	fc = AST.MakerFun(f_id, c.GetTyArgs(), Lib.MkListV[AST.Term](c))

	ggx = AST.MakerFun(g_id, gx.GetTyArgs(), Lib.MkListV[AST.Term](gx))
	gga = AST.MakerFun(g_id, ga.GetTyArgs(), Lib.MkListV[AST.Term](ga))
	ggb = AST.MakerFun(g_id, gb.GetTyArgs(), Lib.MkListV[AST.Term](gb))
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

	a_a_type_list := a.GetTyArgs()
	a_a_type_list.Append(a.GetTyArgs().GetSlice()...)
	faa = AST.MakerFun(f_id, a_a_type_list, Lib.MkListV[AST.Term](a, a))

	b_b_type_list := a.GetTyArgs()
	b_b_type_list.Append(a.GetTyArgs().GetSlice()...)
	fbb = AST.MakerFun(f_id, b_b_type_list, Lib.MkListV[AST.Term](b, b))

	ac_type_list := a.GetTyArgs()
	ac_type_list.Append(c.GetTyArgs().GetSlice()...)
	fac = AST.MakerFun(f_id, ac_type_list, Lib.MkListV[AST.Term](b, c))

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

/* Test STRUCT */

/*Test Add */

func TestAddConst(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	CCstruct.AddTerm(a)

	got := CCstruct.RetrieveEqTerm(a)
	if got == nil {
		t.Errorf("add const didn't work , got nil instead of %v", a.ToString())
	}
}
func TestAddFun(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	CCstruct.AddTerm(fa)

	got := CCstruct.RetrieveEqTerm(fa)
	if got == nil {
		t.Errorf("add fun didn't work , got nil instead of %v", fa.ToString())
	}
}

func TestAddMeta(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	CCstruct.AddTerm(x)

	got := CCstruct.RetrieveEqTerm(x)
	if got == nil {
		t.Errorf("add meta didn't work , got nil instead of %v", x.ToString())
	}
}
func TestAddFunwithMeta(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	CCstruct.AddTerm(fx)

	got := CCstruct.RetrieveEqTerm(fx)
	if got == nil {
		t.Errorf("add fun with meta didn't work , got nil instead of %v", fx.ToString())
	}
}

func TestAddFunArgs(t *testing.T) {
	/* adding a function must add all it's substerms */
	CCstruct := eqStruct.NewCCEqualityStruct()

	CCstruct.AddTerm(gfa)

	if len(CCstruct.Classes()) != 3 {
		t.Errorf("CCstruct must contain 3 classes")
	}
}

func TestAddExisting(t *testing.T) {
	/* adding an existing term must do nothing */
	CCstruct := eqStruct.NewCCEqualityStruct()

	CCstruct.AddTerm(a)
	CCstruct.AddTerm(fa)
	CCstruct.AddTerm(x)
	CCstruct.AddTerm(fx)

	lenbefore := len(CCstruct.Classes())

	CCstruct.AddTerm(a)
	CCstruct.AddTerm(fa)
	CCstruct.AddTerm(x)
	CCstruct.AddTerm(fx)
	lenafter := len(CCstruct.Classes())

	if lenbefore != lenafter {
		t.Errorf("add to many things in Ccstruct len expected : %v ; got : %v", lenafter, lenbefore)
	}
}

/* test retrieve */

func TestRetrieveNil(t *testing.T) {
	/* retrieving non existant term */
	CCstruct := eqStruct.NewCCEqualityStruct()

	CCstruct.AddTerm(a)

	got := CCstruct.RetrieveEqTerm(b)
	if got != nil {
		t.Errorf("retrieve must be nil instead of returning a eqterm")
	}
}

/* Union test */

func TestSimpleUnion(t *testing.T) {
	/* union 2 simple eqterm */
	CCstruct := eqStruct.NewCCEqualityStruct()

	eq1, _ := CCstruct.AddTerm(a)
	eq2, _ := CCstruct.AddTerm(b)

	CCstruct.Union(eq1, eq2)
	if !CCstruct.TestSameparent(eq1, eq2) {
		t.Errorf("%v and %v must be equals", eqStruct.Find(eq1).ToString(), eqStruct.Find(eq2).ToString())
	}
}

func TestUnionRecurs(t *testing.T) {
	/* union of 2 eqstruct with 2 terms */
	CCstruct := eqStruct.NewCCEqualityStruct()

	eq1, _ := CCstruct.AddTerm(a)
	eq2, _ := CCstruct.AddTerm(b)

	eq3, _ := CCstruct.AddTerm(fb)
	eq4, _ := CCstruct.AddTerm(fa)

	CCstruct.Union(eq1, eq3)
	CCstruct.Union(eq2, eq4)
	CCstruct.Union(eq1, eq2)

	if eqStruct.Find(eq3) != eqStruct.Find(eq4) {
		t.Errorf("%v and %v must be equals", eqStruct.Find(eq3).ToString(), eqStruct.Find(eq4).ToString())
	}
}
func TestUnionChain(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	eq1, _ := CCstruct.AddTerm(a)
	eq2, _ := CCstruct.AddTerm(b)
	eq3, _ := CCstruct.AddTerm(c)
	eq4, _ := CCstruct.AddTerm(d)

	CCstruct.Union(eq1, eq2)
	CCstruct.Union(eq2, eq3)
	CCstruct.Union(eq3, eq4)

	if !(CCstruct.TestSameparent(eq1, eq4)) {
		t.Fatal("chain union failed")
	}
}

func TestUnionParent(t *testing.T) {
	/* the parent must be the smallest term */
	CCstruct := eqStruct.NewCCEqualityStruct()

	eq1, _ := CCstruct.AddTerm(a)
	eq2, _ := CCstruct.AddTerm(fa)

	CCstruct.Union(eq1, eq2)

	eq3, _ := CCstruct.AddTerm(fb)
	eq4, _ := CCstruct.AddTerm(b)

	CCstruct.Union(eq3, eq4)

	if !eqStruct.Find(eq2).Equals(CCstruct.RetrieveEqTerm(a)) {
		t.Errorf("the parent must be a and not fa")
	}

	if !eqStruct.Find(eq3).Equals(CCstruct.RetrieveEqTerm(b)) {
		t.Errorf("the parent must be b and not fb")
	}
}

/* test congruence */

func TestCongruence1(t *testing.T) {
	/* f(a) and f(b) must be in the same class if a = b */
	CCstruct := eqStruct.NewCCEqualityStruct()

	eq1, _ := CCstruct.AddTerm(a)
	eq2, _ := CCstruct.AddTerm(b)

	CCstruct.Union(eq1, eq2)

	eqf1, _ := CCstruct.AddTerm(fa)
	eqf2, _ := CCstruct.AddTerm(fb)

	for CCstruct.Congruence() {
	}

	if !CCstruct.TestSameparent(eqf1, eqf2) {
		t.Errorf("f(a) and f(b) must have the same parent")
	}

}

func TestCongruence2(t *testing.T) {
	/* f(a , b) and f(c , d) must be in the same class if a = c , b = d */
	CCstruct := eqStruct.NewCCEqualityStruct()

	eq1, _ := CCstruct.AddTerm(a)
	eq2, _ := CCstruct.AddTerm(b)
	eq3, _ := CCstruct.AddTerm(c)
	eq4, _ := CCstruct.AddTerm(d)

	CCstruct.Union(eq1, eq3)
	CCstruct.Union(eq2, eq4)

	eqf1, _ := CCstruct.AddTerm(fab)
	eqf2, _ := CCstruct.AddTerm(fcd)

	for CCstruct.Congruence() {
	}

	if !CCstruct.TestSameparent(eqf1, eqf2) {
		t.Errorf("f(ab) and f(cd) must have the same parent")
	}

}

func TestCongruence3(t *testing.T) {

	CCstruct := eqStruct.NewCCEqualityStruct()

	eq1, _ := CCstruct.AddTerm(a)
	eq3, _ := CCstruct.AddTerm(c)
	eq4, _ := CCstruct.AddTerm(fab)
	eq5, _ := CCstruct.AddTerm(fbc)

	CCstruct.Union(eq4, eq1)
	CCstruct.Union(eq3, eq5)

	eqf1, _ := CCstruct.AddTerm(f_fab_c)
	eqf2, _ := CCstruct.AddTerm(f_a_fbc)

	for CCstruct.Congruence() {
	}

	if !CCstruct.TestSameparent(eqf1, eqf2) {
		t.Errorf("f_fab_c and f_a_fbc must have the same parent")
	}

}

func TestCongruenceIndependentOfRepresentative(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	eq1, _ := CCstruct.AddTerm(a)
	eq2, _ := CCstruct.AddTerm(b)

	eqf1, _ := CCstruct.AddTerm(fa)
	eqf2, _ := CCstruct.AddTerm(fb)

	CCstruct.Union(eq1, eq2)
	for CCstruct.Congruence() {
	}
	res1 := CCstruct.TestSameparent(eqf1, eqf2)

	CCstruct = eqStruct.NewCCEqualityStruct()

	eq1, _ = CCstruct.AddTerm(a)
	eq2, _ = CCstruct.AddTerm(b)

	eqf1, _ = CCstruct.AddTerm(fa)
	eqf2, _ = CCstruct.AddTerm(fb)

	CCstruct.Union(eq2, eq1)
	for CCstruct.Congruence() {
	}

	res2 := CCstruct.TestSameparent(eqf1, eqf2)

	if res1 != res2 {
		t.Errorf("union order change the congruence")
	}
}

func TestNestedFunctionCongruence(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	e1, _ := CCstruct.AddTerm(a)
	e2, _ := CCstruct.AddTerm(b)

	gg1, _ := CCstruct.AddTerm(gga)
	gg2, _ := CCstruct.AddTerm(ggb)

	CCstruct.Union(e1, e2)

	for CCstruct.Congruence() {
	}

	if !CCstruct.TestSameparent(gg1, gg2) {
		t.Errorf("congruence imbriquée BROKEN")
	}
}

func TestCongruenceTransitivityDeep(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	e1, _ := CCstruct.AddTerm(a)
	e2, _ := CCstruct.AddTerm(b)
	e3, _ := CCstruct.AddTerm(c)

	f1, _ := CCstruct.AddTerm(fa)
	f2, _ := CCstruct.AddTerm(fb)
	f3, _ := CCstruct.AddTerm(fc)

	CCstruct.Union(e1, e2)
	CCstruct.Union(e2, e3)

	for CCstruct.Congruence() {
	}

	if !(CCstruct.TestSameparent(f1, f2) &&
		CCstruct.TestSameparent(f2, f3)) {
		t.Errorf("no transitivity on congruence")
	}
}

func TestCongruenceTermination(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	CCstruct.AddTerm(a)
	CCstruct.AddTerm(gga)

	CCstruct.Union(CCstruct.RetrieveEqTerm(gga), CCstruct.RetrieveEqTerm(a))

	for i := 0; i < 100; i++ {
		if !CCstruct.Congruence() {
			return
		}
	}

	t.Errorf("congruence boucle trop longtemps")
}

/* test func testsameparent */
func TestSameParent(t *testing.T) {

	CCstruct := eqStruct.NewCCEqualityStruct()

	eq1, _ := CCstruct.AddTerm(a)
	eq2, _ := CCstruct.AddTerm(b)
	eq3, _ := CCstruct.AddTerm(c)

	CCstruct.Union(eq3, eq1)
	if !CCstruct.TestSameparent(eq3, eq1) {
		t.Errorf("func test same parent is broken")
	}

	CCstruct.Union(eq1, eq1)
	if !CCstruct.TestSameparent(eq3, eq1) {
		t.Errorf("func test same parent is broken")
	}

	CCstruct.Union(eq3, eq3)
	if !CCstruct.TestSameparent(eq3, eq1) {
		t.Errorf("func test same parent is broken")
	}

	CCstruct.Union(eq3, eq2)

	if !CCstruct.TestSameparent(eq2, eq3) {
		t.Errorf("func test same parent is broken")
	}
}

func TestNoFalseCongruence(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	CCstruct.AddTerm(a)
	CCstruct.AddTerm(b)

	eq4, _ := CCstruct.AddTerm(fa)
	eq5, _ := CCstruct.AddTerm(fb)

	for CCstruct.Congruence() {
	}

	if CCstruct.TestSameparent(eq4, eq5) {
		t.Fatal("false positive congruence detected")
	}
}

func TestNoFalseCongruenceArgs(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	eq3, _ := CCstruct.AddTerm(a)
	eq4, _ := CCstruct.AddTerm(b)

	eq1, _ := CCstruct.AddTerm(fa)
	eq2, _ := CCstruct.AddTerm(fb)

	CCstruct.Union(eq1, eq2)

	for CCstruct.Congruence() {
	}

	if CCstruct.TestSameparent(eq4, eq3) {
		t.Fatal("false positive congruence detected")
	}
}

/*update parent */

func TestUpdateParent1(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()
	eq1, _ := CCstruct.AddTerm(a)
	eq2, _ := CCstruct.AddTerm(b)
	CCstruct.AddTerm(c)
	eq5, _ := CCstruct.AddTerm(fab)
	eq6, _ := CCstruct.AddTerm(fbc)

	CCstruct.Union(eq1, eq2)
	for CCstruct.UpdateParent() {
	}

	Lib.MkLazy(func() string { return fmt.Sprintf("Expected : %v", CCstruct.ToString()) })

	np1 := CCstruct.RetrieveEqTerm(faa)
	np2 := CCstruct.RetrieveEqTerm(fbb)
	np3 := CCstruct.RetrieveEqTerm(fac)
	np4 := CCstruct.RetrieveEqTerm(fbc)

	if np1 == nil && np2 == nil {
		t.Errorf(fmt.Sprintf("the new parent is not present"))
	}
	if np3 == nil && np4 == nil {
		t.Errorf("the new parent is not present")
	}
	if np1 == nil {
		if !CCstruct.TestSameparent(eq5, np2) {
			t.Errorf("the parent isn't updated")
		}
	} else {
		if !CCstruct.TestSameparent(eq5, np1) {
			t.Errorf("the parent isn't updated")
		}

		if np3 == nil {
			if !CCstruct.TestSameparent(eq6, np4) {
				t.Errorf("the parent isn't updated")
			} else {
				if !CCstruct.TestSameparent(eq6, np3) {
					t.Errorf("the parent isn't updated")
				}
			}

		}
	}
}

func TestUpdateParentIdempotence(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	eq1, _ := CCstruct.AddTerm(a)
	eq2, _ := CCstruct.AddTerm(b)

	CCstruct.Union(eq1, eq2)

	for CCstruct.Congruence() {
	}
	for CCstruct.UpdateParent() {
	}

	size1 := len(CCstruct.Classes())

	for CCstruct.UpdateParent() {
	}

	size2 := len(CCstruct.Classes())

	if size1 != size2 {
		t.Errorf("UpdateParent adding useless terms")
	}
}

func TestFullPipelineConsistency(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	e1, _ := CCstruct.AddTerm(a)
	e2, _ := CCstruct.AddTerm(b)
	e3, _ := CCstruct.AddTerm(c)

	f1, _ := CCstruct.AddTerm(fc)
	f2, _ := CCstruct.AddTerm(fb)

	CCstruct.Union(e1, e2)
	CCstruct.Union(e2, e3)

	for CCstruct.Congruence() {
	}
	for CCstruct.UpdateParent() {
	}

	if !CCstruct.TestSameparent(f1, f2) {
		t.Errorf("pipeline cassé (union + congruence + update)")
	}
}

func TestCopy1(t *testing.T) {
	CCstruct := eqStruct.NewCCEqualityStruct()

	eq1, _ := CCstruct.AddTerm(a)
	eq2, _ := CCstruct.AddTerm(b)

	CCstruct.Union(eq1, eq2)
	cccopy := CCstruct.Copy()
	eq5, _ := CCstruct.AddTerm(fa)
	eq3, _ := cccopy.AddTerm(fa)
	eq4, _ := cccopy.AddTerm(fb)

	cccopy.Union(eq3, eq4)
	CCstruct.Union(eq2, eq5)

	if !CCstruct.TestSameparent(eq1, eq2) {
		t.Errorf("%v", CCstruct.ToString())
	}
	if !cccopy.TestSameparent(eq1, eq2) {
		t.Errorf("%v ", cccopy.ToString())
	}

}
