IMPLEMENTATION MODULE TESTLAT;

IMPORT BASISLR, BASISSI, REDBAS2, REDBAS3, MRG;

FROM SYSTEM   IMPORT ADDRESS, CAST;
FROM Storage  IMPORT ALLOCATE, DEALLOCATE;
FROM CHRONO   IMPORT InitChrono, Chrono, TimeFormat, ValChrono, WriteChrono;
FROM MYINOUT  IMPORT WriteInt, WriteLn, WriteString, WriteBool, FILE, Error,
                     Assert;
FROM NUM      IMPORT Pow, IToLI, IToLR, WriteLR, Sqrt, Lg, MaxLongReal,
                     ModLR, Trunc, TruncLR;
FROM NUM2     IMPORT Factorielle;

FROM SUPINT   IMPORT SuperInteger, Create, Affect, Exposant, NumDigits, 
                     Exchange, WriteSup;
FROM SUPARITH IMPORT ShiftLeft, Equal, Zero, Negative, Smaller, ChangeSign, 
                     Add, Subtract, Quotient, Multiply, Modulo, Divide, GCD,
		     Euclide, DivideMod, PowerSupInt, AbsSizeOrd, DivideLR,
                     Log2;
FROM SUPFACT  IMPORT Factors, IsPrime;
FROM SUPCONV  IMPORT IntToSup, SupToLongReal;
(*
FROM MRG      IMPORT Test, TestLa;
*)
FROM LATBASIS IMPORT Basis, InitBasis, CreateBasis, WriteBasis, Dualize,
                     DeleteBasis, UpdateVVWW;
FROM REDBAS   IMPORT PreRedDieterSV, PreRedLLLSV, PreRedLLLRM, PreRedDieter,
                     ReductMinkowski, ShortestVector, InitREDBAS, VerifyType;
FROM MULT     IMPORT MScal, MAffect, MVect, MSetm, MCreateVect, MDeleteScal,
		     MCreateScal, MAdd, MProdModm, MPowerPolyMod, MWriteScal,
                     MWriteVect, LIToMScal, MScalToLR, MScalToSup, 
                     PrimElem, MaxPeriod, SetFactors,MGetm,MDeleteVect;
FROM BASIS    IMPORT BScal, BZero, BOne, BAdd, BMultiply, BChangeSign, BVect,
		     BMatr, BCreateScal, BCreateVect, BAffect, BCopyVect, 
		     BAffectIdentMatr, BWriteScal, BDivideRound, BProdScal, 
		     BProdScalLR, BProdScalSI,BDeleteVect, BEuclide;
FROM BASISLR  IMPORT VectLI;
FROM CONFIG   IMPORT MMaxDim, MDim, BDim, BMaxDim, OutputType, MCoord, Categ,
                     DimProj;
FROM NORM     IMPORT NormType, CriterionType, GammaType, Normaliz,
                     InitNormaliz, CreateNormaliz, DeleteNormaliz;

FROM CONVERT  IMPORT MScalToBScal, BScalToMScal, BScalToSup, SupToBScal;




VAR
   chrono : Chrono;
   Hst, MG : BMatr; 
   Kk : ARRAY  BDim  OF  BMatr;
   term, term1, term2, T1, T2 : BScal;

(*-------------------------------------------------------------------------*)

PROCEDURE CreateTestConfig (VAR T : TestConfig);
   BEGIN
   NEW (T);
   WITH T^ DO
      k := 0;  NbCoord := 0;  Maxds := 0;  NbCats := 1;  
      Criterion := Spectral;   
      Verify := Verify0;      Output := CurOut;
      InvertL := FALSE;       InvertS := FALSE;
      CreateNormaliz (Normal);
      END;
   END CreateTestConfig;

(*-------------------------------------------------------------------------*)

PROCEDURE DeleteTestConfig (VAR T : TestConfig);
   VAR
      i : MDim;
      j : MCoord;
      d : DimProj;
   BEGIN
   WITH T^ DO
      DeleteNormaliz (Normal);
      FOR i := 1 TO k DO
         FOR j := 1 TO NbCoord DO MDeleteScal (MasterGen [i,j]) END;
         END;
      DeleteBasis (TBas);   DeleteBasis (RBas[0]);   
      FOR d := 1 TO Maxdp DO
         DeleteBasis (RBas[d]);
         BASISLR.BDeleteVect (L2[d], 1, Maxds);
         BASISLR.BDeleteVect (S2[d], 1, Maxds);
         END
      END;
   DISPOSE (T);
   END DeleteTestConfig;

(*-------------------------------------------------------------------------*)

PROCEDURE InitTestConfig 
   (T : TestConfig;  Norm : NormType;
    m  : MScal;   k  : MDim;      NbCoord : MCoord;  
    ds : BDim;    dp : DimProj;   NbCats  : Categ;
    gamma : GammaType;   beta : LONGREAL
   );
   VAR
      i : MDim;
      t, Dim : BDim;
      j : MCoord;
      d : DimProj;
      c : Categ;
   BEGIN
   Assert (T <> NIL, "InitTestConfig:    TestConfig is a NIL pointer");
   InitNormaliz (T^.Normal, "", Norm, gamma, beta, NbCoord, m, k);
   MAffect (m, T^.m);
   T^.k := k;   
   T^.NbCoord := NbCoord;
   T^.NbCats := NbCats;
   WITH T^ DO
      Maxds := ds;  Maxdp := dp;   C := NbCats;
      FOR i := 1 TO k DO
         (* Must create elements individually because k # t.  *)
         FOR j := 1 TO NbCoord DO MCreateScal (MasterGen [i,j]) END;
         END;
      CreateBasis (TBas);    InitBasis (TBas, m, Norm, dp);
      FOR d := 0 TO Maxdp DO
         (* If d > 0, RBas[d] will be a basis in d dimensions.  *)
         IF d = 0 THEN Dim := ds ELSE Dim := d END;
         CreateBasis (RBas[d]);  InitBasis (RBas[d], m, Norm, Dim);
         BASISLR.BCreateVect (L2[d], 1, Maxds);
         BASISLR.BCreateVect (S2[d], 1, Maxds);
         END;
      FOR c := 1 TO NbCats DO
         ValCrit[c] := 1.0;
	 Mins2 [c]  := 0.0;
         Maxs2 [c]  := 1.0;
	 END;
      FOR d := 1 TO Maxdp DO
	 FOR t := 1 TO BMaxDim DO  
	    S2 [d, t] := 0.0;
            L2 [d, t] := 0.0;  
	    END;
         END;
      END
   END InitTestConfig;

(*************************************************************************)
 
PROCEDURE PrintLine (T : TestConfig;  t : CARDINAL;  l2, s2 : LONGREAL);
   (* Imprime une ligne de resultats (un test).                          *)
   (* Pour les projections, indique seulement le nb. de coordonnees, t.  *)
   VAR
      LaTeX : BOOLEAN;
   BEGIN
   WITH T^ DO
      LaTeX := (Output = CurOutTex);
      WriteInt (t, 5);   
      IF LaTeX THEN  WriteString ( '  & ' ) ELSE WriteString ( '    ' ) END;
      IF (Criterion = Spectral) OR (Criterion = SpectralP) THEN
         l2 := Sqrt (l2)
         END;
      IF InvertL THEN  l2 := 1.0/l2 END;
      IF InvertS THEN  s2 := 1.0/s2 END;
      IF l2 > 0.0 THEN
         WriteLR (l2, 12, 5, 4) 
      ELSE 
         WriteString ("            ")
         END;
      IF LaTeX THEN  WriteString ( ' &' )  ELSE  WriteString ( '  ' ) END;
      WriteLR (s2, 12, 5, 4);
      IF LaTeX THEN  WriteString ( ' &' )  ELSE  WriteString ( '  ' ) END;
      END;
   WriteLR (ValChrono (chrono, sec), 10, 2, 1);  
   IF LaTeX THEN  WriteString ( ' \\' )  END;
   WriteLn;
   END PrintLine;

(***************************************************************************)

PROCEDURE BeyerTest (T: TestConfig;  B: Basis;  Verif: VerifyType;
                     VAR s2: LONGREAL);
   BEGIN
   Dualize (B);
   PreRedDieter (B, 0);
   Dualize (B);

   WITH T^ DO
      OK := ReductMinkowski (B, 0);
      IF NOT OK THEN
         WriteString ('TESTLAT.BeyerTest: Basis was not reduced:'); 
         WriteLn;  WriteBasis (B);
         s2 := 0.0;   RETURN;
         END;
      CASE Verify OF  
         Verify2:
            OK := REDBAS2.VerifMinkowski (B, 0);
       | Verify3:
            OK := REDBAS3.VerifMinkowski (B, 0);
         ELSE
            OK := TRUE;
         END;
      IF NOT OK THEN
         WriteString ('TESTLAT.BeyerTest: Verif not OK. ');
         WriteLn;    WriteBasis (B);
         END;
      s2 := B^.VVLR[1] / B^.VVLR[B^.Dim];
      IF Output # None THEN  PrintLine (T, B^.Dim, 0.0, s2) END;
      OK := TRUE;
      END;
   END BeyerTest;

(*************************************************************************)

PROCEDURE SpectralTest (T : TestConfig;  B : Basis;  Criterion: CriterionType;
                        Verif: VerifyType;  VAR l2, s2 : LONGREAL);
   VAR
      z : VectLI;
   BEGIN
   WITH T^ DO
      IF (Criterion # SpectralP) THEN  Dualize (B)  END;
      OK := ShortestVector (B);           (* Calcul du test spectral.  *)
      IF NOT OK THEN
         WriteString ("TESTLAT.SpectralTest: ShortestVector failed.");
         WriteLn;  WriteBasis (B);
         RETURN;
         END;
      CASE Verify OF  
         Verify2:
            OK := REDBAS2.VerifShortest (B);
       | Verify3:
            OK := REDBAS3.VerifShortest (B, 0, (B^.Dim DIV 2), z);
         ELSE
            OK := TRUE;
         END;
      IF NOT OK THEN
         WriteString ('TESTLAT.SpectralTest: Verify not OK. ');
         WriteLn;   WriteBasis (B);
         END;
      (* Computation of l2 (squared length of shortest vector) and s2. *)
      WITH B^ DO
         l2 := VVLR[1];
         s2 := l2 / T^.Normal^.Cst[Dim];
         IF Output # None THEN  PrintLine (T, Dim, l2, s2) END;
         END;
      IF (Criterion # SpectralP) THEN  Dualize (B)  END;
      OK := TRUE;
      END;
   END SpectralTest;

(*************************************************************************)

PROCEDURE PalphaTest (T : TestConfig;  B : Basis;  VAR s2 : LONGREAL);
   BEGIN
   Error ("PalphaTest pas encore implantee");
   END PalphaTest;

(*************************************************************************)

PROCEDURE AddToBasis (T : TestConfig;  d : BDim;  Ind : CoordSet;  n : BDim);
   (** -> Add coord. n to TBas and re-triangulate. **)
   (* Assumes that Ind contains d coordinates, the last one being n.  *)
   (* Thus, after adding coord. n, we have a d-dimensional basis.     *)
   VAR
      i, j : CARDINAL;
      k : MDim;
      Q11, Q12, Q21, Q22, mtemp : BScal;
   BEGIN
   k := T^.k;
   (* La d-ieme colonne *)
   WITH  T^.TBas^  DO
      FOR  i := 1  TO  d-1  DO
         BAffect (BZero, V[i,d]);
         FOR  j := 1  TO  k  DO
            BMultiply (Hst[i,j], MG[j,n], term);
            BAdd (V[i,d], term, V[i,d])
            END
         END;
      (* La d-ieme entree de la d-ieme colonne *)
      IF  d = 1  THEN
         BAffect (MG[1,n], T1)
      ELSE
         BAffect (BZero, T1);
         FOR  j := 1  TO  k  DO
            BMultiply (Kk[d-1,1,j], MG[j,n], term);
            BAdd (T1, term, T1)
            END
         END;
      FOR  i := 2  TO  k  DO
         IF  d = 1  THEN
            BAffect (MG[i,n], T2)
         ELSE
            BAffect (BZero, T2);
            FOR  j := 1  TO  k  DO
               BMultiply (Kk[d-1,i,j], MG[j,n], term);
               BAdd (T2, term, T2)
               END
            END;
         BEuclide (T1, T2, Q11, Q12, Q21, Q22, T1);
         FOR  j := 1  TO  k  DO
            BMultiply (Q21, Kk[d,i-1,j], term1);
            BMultiply (Q22, Kk[d-1,i,j], term2);
            BAdd (term1, term2, Kk[d,i-1,j]);
            BMultiply (Q11, Kk[d,i-1,j], term1);
            BMultiply (Q12, Kk[d-1,i,j], term2);
            BAdd (term1, term2, Kk[d,i,j])
            END
         END;
      MScalToBScal (T^.m, mtemp);
      BEuclide (T1, mtemp, Q11, Q12, Q21, Q22, T^.TBas^.V[d,d]);
      FOR  j := 1  TO  k  DO
         BMultiply (Q21, Kk[d-1,k,j], Kk[d,k,j]);
         BMultiply (Q11, Kk[d-1,k,j], Hst[d,j])
         END
      END
   END AddToBasis;

(*************************************************************************)

PROCEDURE RemoveFromBasis (T : TestConfig;  d : BDim;
                           Ind : CoordSet;  j : BDim);
   (** -> Remove coordinate j from TBas.  **)

   BEGIN
   END RemoveFromBasis;

(*************************************************************************)

PROCEDURE CheckRank (B : Basis;  d : BDim);
   (* Checks if this d-dimensional basis has full rank.  *)
   BEGIN
   END CheckRank;

(*************************************************************************)

PROCEDURE TestBasis (T : TestConfig;  c : Categ;  d : BDim);
   VAR
      l2, s2: LONGREAL;
      B : Basis;
   BEGIN
   (*
   ->  Appliquer le bon test:  Shortestvector, ou ReductMinkowski, ...;
   ->  Normaliser en utilisant Cst[t] pour obtenir S;
   ->  Mettre a jour L2 et S2;
   *)

   WITH T^ DO
      IF d = 1 THEN B := RBas[0] ELSE B := RBas[d] END;
      IF Criterion = Beyer THEN
         BeyerTest (T, B, Verify, s2);
      ELSIF Criterion = Palpha THEN
         PalphaTest (T, B, s2);
      ELSE
	 SpectralTest (T, B, Criterion, Verify, l2, s2);
	 END;
      IF (s2 < Mins2[c]) OR (s2 > Maxs2[c]) THEN
         (* Ce RNG n'est pas assez bon pour la cat. c ou les cat. > c.   *)
         DEC (c);  C := c;  RETURN 
         END;
   (*   IF (s2 < S2[d][Dim]) THEN  S2[d][Dim] := s2;  L2[d][Dim] := l2 END;*)
      IF (s2 < ValCrit [c]) THEN ValCrit [c] := s2 END;
      (* On met a jour seul. pour c, on ajustera pour les c' > c apres. *)
      END;
   END TestBasis;

(*************************************************************************)

PROCEDURE TestProjections 
   ( T : TestConfig;  
     c : Categ;             (* Current smallest category.         *)
     d : BDim;              (* Dimension of the projections.      *)
     i : BDim;              (* Largest index in Ind.              *)
     Ind : CoordSet         (* Set of d-1 coordinates.            *)
   );
   (* Examines all the d-dimensional projections whose first d-1         *)
   (* indices are in Ind.                                                *)
   (* These projections are considered only for the categories >= c.     *)
   VAR
      j : BDim;
   BEGIN
   j := i+1;
   WITH T^ DO
      WHILE (j <= RangeProj [C, d]) DO
	 Ind := Ind + CoordSet{j};
	 WHILE j > RangeProj [c, d] DO INC (c) END;
	 IF c > C THEN RETURN END;
	 (** -> Add coord. j (and 1 dim.) to TBas and re-triangulate. **)
	 (** -> Copy RBas[d-1] to RBas[d], add one dim. using TBas,
		and reduce.   (See old BuildLaBasis and IncDimLaBasis.)
	  **)
	 AddToBasis (T, d, Ind, j);
	 (**  ....  **)
	 IF (d = k) THEN
	    CheckRank (TBas, d)
	 ELSIF d > k THEN
	    TestBasis (T, c, d);
	    END;
	 TestProjections (T, c, d+1, j, Ind);
	 (** -> Remove vector j from TBas.  **)
	 RemoveFromBasis (T, d, Ind, j);
	 Ind := Ind - CoordSet{j};
	 INC (j);
	 END
      END
   END TestProjections;

(*************************************************************************)

PROCEDURE TestLattice (T : TestConfig);
   (* Assumes that MasterGen contains the k generating vectors.         *)
   (* Examines all the projections of the lattice that are specified,   *)
   (* for all the categories.                                           *)
   VAR
      c   : Categ;
      Ind : CoordSet;
      t   : BDim;
   BEGIN
   WITH T^ DO
      C := NbCats;
      IF DimenProj [C] > 1 THEN
         (* On doit examiner des projections sur dim. non successives.  *)
         (* We first do RBas[1] <- TBas <- Basis of dimension 1.        *)
         Ind := CoordSet{1};
         WITH TBas^ DO
            Dim := 1;  MScalToBScal (MasterGen[1,1], V[1,1]);
            (** -> Init V[1,1] et W[1,1] a une base (et m-dual) en 1 dim.
               pour la premiere coordonnee.
               Habituellement, V[1,1] = 1 et W[1,1] = m.  
               Copier ensuite cette base dans RBas[1] et reduire.  
            **)
            END;
         TestProjections (T, 1, 2, 1, Ind);
         END; 

      IF C > 0 THEN
         (* Ce Gener. peut encore etre considere pour une categ.   *)
         (* On regarde maintenant les coordonnees successives.     *)
         t := k + 1;  
         (** RBas[0] <- coordinates 1,.., t of MasterGen.  Reduce.  **)
         (** Ind <- {1,...,t};      **)
         WHILE t < RangeProj [C, 1] DO
            INC (t);  Ind := Ind + CoordSet{t};
            (** -> Add coordinate t to Basis, update dual, reduce. **)
            AddToBasis (T, t, Ind, t);
            TestBasis (T, C, 1);    (* Use RBas[0] *)
            END
         END;

      (* We now check if this generator is good enough to be saved.  *)
      FOR c := 2 TO C DO
         IF ValCrit[c] > ValCrit[c-1] THEN ValCrit[c] := ValCrit[c-1] END;
         END
      END
   END TestLattice;

(****************************************************************************)

BEGIN
END TESTLAT.
