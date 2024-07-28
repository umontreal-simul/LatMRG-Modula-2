IMPLEMENTATION MODULE MRG;


FROM SYSTEM   IMPORT ADDRESS;
FROM CHRONO   IMPORT InitChrono, Chrono, TimeFormat, ValChrono;
FROM MYINOUT  IMPORT WriteInt, WriteLn, WriteString, Error;
FROM NUM      IMPORT Pow, IToLR, WriteLR, Sqrt, Lg, TruncLR;
FROM NUM2     IMPORT Factorielle;

FROM SUPINT   IMPORT SuperInteger, Create, Affect, Exposant, NumDigits, 
                     Exchange, WriteSup;
FROM SUPARITH IMPORT Equal, Zero, Negative, Smaller, ChangeSign, Subtract,
                     Add, Quotient, Multiply, Modulo, GCD, Euclide, DivideLR,
                     Log2;
FROM SUPFACT  IMPORT Factors, IsPrime;
FROM SUPCONV  IMPORT IntToSup, SupToLongReal;

FROM CONFIG   IMPORT BDim, BMaxDim, MDim, MMaxDim, OutputType, MCoord;
FROM CONVERT  IMPORT MScalToBScal, BScalToMScal, BScalToSup, SupToBScal;
FROM MULT     IMPORT MScal, MAffect, MVect, MSetm, MCreateVect, 
		     MCreateScal, MAdd, MProdModm, MPowerPolyMod, MWriteScal,
                     MWriteVect, LIToMScal, MScalToLR, MScalToSup, 
                     PrimElem, MaxPeriod, SetFactors,MGetm,MDeleteVect;
FROM BASIS    IMPORT BScal, BZero, BOne, BAdd, BMultiply, BChangeSign, BVect,
		     BMatr, BCreateScal, BCreateVect, BAffect, BCopyVect, 
		     BAffectIdentMatr, BWriteScal, BDivideRound, BProdScal, 
		     BProdScalLR, BProdScalSI,BDeleteVect, BConvLR;
FROM BASISLR  IMPORT VectLI;
FROM NORM     IMPORT CriterionType, NormType, GammaType, Normaliz, 
                     CreateNormaliz, InitNormaliz;
FROM LATBASIS IMPORT Basis, InitBasis, CreateBasis, WriteBasis, Dualize,
                     DeleteBasis;
FROM TESTLAT  IMPORT TestConfig;
FROM REDBAS   IMPORT VerifyType, PreRedDieter, ReductMinkowski, ShortestVector,
                     PreRedDieterSV, PreRedLLLSV, PreRedLLLRM, InitREDBAS;

IMPORT BASISLR, BASISSI, REDBAS2, REDBAS3;



VAR
   mB              : BScal;           (* Module m en BScal                  *)
(* - Dans InitMRG, IncDimBasis,  BuildBasis 
   - Pourrait etre remplace par {LATBASIS_Basis.mLR,  LATBASIS_Basis.mSI} avec
     un IF (SISQUARES).
   - QUESTION? Dans LATBASIS_Basis, pourquoi n'a t-on pas remplac'e {mLR, mSI}
        par m: BScal, {mLR2, mSI2} par m2: BScal, {VVLR, VVSI} {WWLR, WWSI} 
        PAR VV, WW: BVect; comme pour V, W: BMatr??
*)

   Order           : MDim;            (* Ordre du generateur a tester       *)
(* - dans toutes les PROCEDURES
   - Peut-etre dans une structure MRG_InfoMRG avec champs Bas, m, k, a ???
*)

   lgVolDual2      : ARRAY  BDim  OF  LONGREAL;
                                      (* 2 * log_2 (nb. de pts).            *)
(* - Calcule dans InitStates a partir de mSI et Sta[1,1];
    Utilise dans SpectralTest, BeyerSpectralTest pour calculer S2.
   - Doit-elle etre calculee plusieurs fois dans InitStates?? Peut-etre
        une petite procedure locale. Cette variable est laide, je ne suis
  pas sur de ce qu'elle fait. Si on pouvait l'eliminer...
*)

   lgm2            : LONGREAL;        (* 2 * log_2 (m).                     *)
(* - Calcule dans InitMRG; utilise dans InitStates pour calculer lgVolDual2
   - pas souvent utilise; un nouveau champ de LATBASIS_Basis  ??
*)

   T1, T2, T3, T4, T5, T6, T7, T8  : SuperInteger;  (* Variables de travail *)
(* - T5, T6, T7, T8 dans BuildVectLaBasis, BuildLaBasis, Insertion 
   - T1, T2, T3, T4 dans beaucoup de PROCEDURES 
  Je pense que de telles variables de travail globales sont acceptables
  a la condition de s'imposer une discipline: on ne les utilise jamais
  pour transmettre des valeurs d'une procedure a une autre ou au programme
  principal. Quand on entre
  dans une procedure, on doit les initialiser explicitement avant de les
  utiliser; quand on sort d'une procedure, on les considere comme garbage.
  On ne voudrait pas les creer 100000... fois, mais seulement 1 fois
  au debut du programme, car ce sont des SuperInteger.
*)

   l, ll           : MDim;            (* Indices; dans  BEGIN  *)

   mSI             : SuperInteger;    (* Module en SuperEntier              *)
(* - Dans InitMRG, Insertion,  Lemme2, InitStates, BuildLaBasis,
     BuildVectLaBasis 
   - Devrait etre remplace partout par Basis.mSI ou infoMRG^.m
*)

   VSI, WSI        : BASISSI.BMatr;   (* Matrices pour construire les bases *)
(* - InitMRG, DeleteMRG, BuildLaBasis, BuildVectLaBasis, IncDimLaBasis,
        IncDimBasis 
*)

   LacI            : BVect;           (* Lacunary indices.                  *)
(* - InitMRG DeleteMRG PrintHeadRES PrintHeadTEX TestLa TestCri Test 
   - un nouveau champ de MRG_InfoMRG ??

*)

   e               : MScal;        (* Exposant. *)
(* - InitStates BuildLaBasis BuildVectLaBasis 
   - Pour transformer un BScal en MScal
   - Utilise dans MPowerPolyMod (a, Order, e, xi);
*)

   q               : BVect;
(* - InitMRG DeleteMRG:  INUTILISE 
*)

   i               : BDim;
(* - Indice:  BEGIN du MODULE 
   - Initialisation de Mins2, Minq2, Q2, S2 devraient-elles etre dans TESTLAT??
*)

   xi              : MVect;
(* - InitMRG DeleteMRG InitStates BuildLaBasis BuildVectLaBasis
   - un champ de InfoMRG ??? 
*)

   chrono          : Chrono;
(*  Dans PrintLineL1, PrintLine, Test, TestCri
*)

   IMax            : BDim;
(* - Dimension maximale des bases Lacunaires.
   - Dans BuildVectLaBasis BuildLaBasis IncDimLaBasis
   - Definie dans  BuildVectLaBasis, BuildLaBasis.
   - devrait etre passee en parametre dans IncDimLaBasis 
*)

   aSI             : ARRAY MDim OF SuperInteger;
              (* Coefficients du generateur ?? *)
(*  - Dans IncDimBasis InitStates Test TestCri
    - Mettre dans InfoMRG
*)

   Sta             : ARRAY MDim OF ARRAY MDim OF SuperInteger;
(*  - Dans Insertion Lemme2 InitStates BuildBasis BuildLaBasis 
  -  Sta  pourrait etre declare dans BuildBasis BuildLaBasis;
       est-ce trop couteux??
  - Sta Devrait etre passe en VAR a Insertion Lemme2 InitStates;
*)

   IP              : ARRAY MDim OF BOOLEAN; (* Indique si l'element
                             diagonal de Sta est nul (TRUE) ou non (FALSE) *)
(* - Dans Insertion  Lemme2 InitStates BuildBasis BuildLaBasis 
  -  IP  devrait etre declare dans BuildBasis BuildLaBasis;
  - IP Devrait etre passe en VAR a Insertion Lemme2 InitStates;
*)

   print           : BOOLEAN; (* Si TRUE, imprime les resultats *)
(* - BeyerTest SpectralTest BeyerSpectralTest Test TestCri 
   - Remplacer par Out: CONFIG_OutputType
*)

   LaTeX           : BOOLEAN;         (* Si imprime les resultats en LaTeX. *)
(* - PrintLine PrintLineL1 Test TestCri 
   - Remplacer par Out: CONFIG_OutputType
*)

   curmaxMDim      : MDim;
   curmaxBDim      : BDim;
(* - InitMRG DeleteMRG;    INUTILISE
*)

   MIC             : ARRAY  BDim  OF  BITSET;
(* Dans BuildVectLaBasis; pas termine, puisque non initialise 
*)

(* ===================================================

Les PROCEDURE
  	PrintLine, PrintLineL1, BeyerTest, SpectralTest, BeyerSpectralTest
devraient-elles etre importees de TESTLAT?
Pas necessaire si on importe TestLattice, alors on pourrait les
 eliminer de MRG.
*)


(*************************************************************************)

PROCEDURE InitMRG (m : MScal; k : MDim; d : BDim);
   VAR
      d1  : BDim;
      k1  : MDim;
   BEGIN
(*   CreateBasis (Bas); *)
   MSetm (m);    MScalToBScal (m, mB);
   Order := k;
   IF  Order > curmaxMDim  THEN
      IF  curmaxMDim = 0  THEN  k1 := 0  ELSE  k1 := curmaxMDim + 1  END;
      MCreateVect (xi, k1, Order);
      curmaxMDim := Order;
      END;
   IF  d > curmaxBDim  THEN
      IF  curmaxBDim = 0  THEN  d1 := 0  ELSE  d1 := curmaxBDim + 1  END;
      InitBasis (Bas, m, UsedNorm, d);
      BASISSI.BCreateMatr (VSI, d1, d);  BASISSI.BCreateMatr(WSI, d1, d);
      BCreateVect (LacI, d1, d);
      BCreateVect (q, d1, d);
      curmaxBDim := d
      END;
   WITH  Bas^  DO
      lgm2 := 2.0 * Log2 (mSI);
      END;
   Affect (Bas^.mSI, mSI);
   
   END InitMRG;
   
(*************************************************************************)

PROCEDURE DeleteMRG (d : BDim);
   VAR
      d1  : BDim;
      k1  : MDim;
   BEGIN
   IF  Order > curmaxMDim  THEN
      IF  curmaxMDim = 0  THEN  k1 := 0  ELSE  k1 := curmaxMDim + 1  END;
      MDeleteVect (xi, k1, Order); 
      curmaxMDim := Order;
      END;
   IF  d > curmaxBDim  THEN
      IF  curmaxBDim = 0  THEN  d1 := 0  ELSE  d1 := curmaxBDim + 1  END;
      BASISSI.BDeleteMatr (VSI, d1, d);  BASISSI.BDeleteMatr(WSI, d1, d);
      BDeleteVect (LacI, d1, d);
      BDeleteVect (q, d1, d);      
      DeleteBasis(Bas);
      END;
   END DeleteMRG;   

(*************************************************************************)

PROCEDURE IncDimBasis (B : Basis);
   (*  x_n = a_1 x_{n-1} + a_2 x_{n-2} +...+ a_ord x_{n-ord} (mod. m).   *)
   (*  On a Dim >= Order.                                                *)
   VAR
      i, j : BDim;
   BEGIN
   WITH  B^  DO
      INC (Dim);
      FOR  i := 1  TO  Dim-1  DO
	 IntToSup (0, VSI[0,i]);
	 FOR  j := 1  TO  Order  DO
	    BScalToSup (V[i,Dim-j], T1);
	    Multiply (aSI[j], T1, T1);   Add (VSI[0,i], T1, VSI[0,i])
	    END;
	 Modulo (VSI[0,i], mSI, VSI[0,i]);
	 SupToBScal (VSI[0,i], V[i,Dim])
	 END;
      FOR  j := 1  TO  Dim-1  DO  BAffect (BZero, V[Dim,j])  END;
      BAffect (mB, V[Dim,Dim]);
      FOR  i := 1  TO  Dim-1  DO  BAffect (BZero, W[i,Dim])  END;
      BAffect (BOne, W[Dim,Dim]);
      FOR  j := 1  TO  Dim-1  DO
	 IntToSup (0, T1);
	 FOR  i := 1  TO  Dim-1  DO
	    BScalToSup (W[i,j], T2);
	    Multiply (VSI[0,i], T2, T2);   Subtract (T1, T2, T1)
	    END;
	 Quotient (T1, mSI, T1);   SupToBScal (T1, W[Dim,j])
	 END;
      IF  SISquares  THEN
	 FOR  i := 1  TO  Dim  DO
            VVSI[i]^.Negative := TRUE;   WWSI[i]^.Negative := TRUE;
(*	    BASISSI.BSetNeg (VVSI[i]);   BASISSI.BSetNeg (WWSI[i]) *)
	    END
      ELSE
	 FOR i := 1 TO Dim DO  VVLR[i] := -1.0;  WWLR[i] := -1.0  END
	 END
      END
   END IncDimBasis;

(**************************************************************************)

PROCEDURE Insertion;
(* Devrait etre PROCEDURE Insertion (VAR Sta; VAR IP )  ?? RS
*)
   (*  Cette procedure insere le vecteur Sta[0] dans la matrice           *)
   (*  triangulaire Sta. Si IP[i] = TRUE, l'entree diagonale sur la       *)
   (*  i-ieme ligne de Sta est non-nulle (modulo mSI) et divise mSI.      *)
   (*  Sinon, la i-ieme ligne est identiquement nulle. L'insertion doit   *)
   (*  preserver ces proprietes.                                          *)
   (*  Le vecteur Sta[0] est altere au cours de l'operation.              *)
      VAR
	 j, j1 : BDim;
      BEGIN
      FOR  j := 1  TO  Order  DO
	 Modulo (Sta[0,j], mSI, Sta[0,j]);
	 IF  NOT Zero (Sta[0,j])  THEN
	    IF  NOT IP[j]  THEN
	       Euclide (Sta[0,j], mSI, T1, T2, T3, T4, Sta[j,j]); 
	       FOR  j1 := j+1  TO  Order  DO
		  Multiply (T1, Sta[0,j1], Sta[j,j1]);
		  Modulo (Sta[j,j1], mSI, Sta[j,j1])   
		  END;
	       IP[j] := TRUE;
	       RETURN
	    ELSE
	       Euclide (Sta[j,j], Sta[0,j], T1, T2, T3, T4, Sta[j,j]);
	       IntToSup(0, Sta[0,j]);
	       FOR  j1 := j+1  TO  Order  DO
		  Multiply (T1, Sta[j,j1], T5);
		  Multiply (T2, Sta[0,j1], T6);
		  Multiply (T3, Sta[j,j1], T7);
		  Multiply (T4, Sta[0,j1], T8);
		  Add (T5, T6, Sta[j,j1]);  
                  Modulo (Sta[j,j1], mSI, Sta[j,j1]);
		  Add (T7, T8, Sta[0,j1])
		  END
	       END
	    END
	 END
      END Insertion;

(**************************************************************************)

PROCEDURE Lemme2;
(* Devrait etre PROCEDURE Lemme2 (VAR Sta; VAR IP )  ?? RS
*)

   (*  Cette procedure suppose que la matrice Sta est triangulaire. Si    *)
   (*  IP[i] = TRUE, l'entree diagonale sur la i-ieme ligne de Sta est    *)
   (*  non-nulle (modulo mSI) et divise mSI. Sinon, la i-ieme ligne est   *)
   (*  identiquement nulle.                                               *)
   VAR
      i, j : MDim;
   BEGIN
   FOR  i := 1  TO  Order  DO
      IF  IP[i]  THEN
	 Quotient (mSI, Sta[i,i], T1);      
	 IF  Negative (T1)  THEN  ChangeSign (T1, T1)  END;
	 IF  Smaller (T1, mSI)  THEN
	    FOR  j := 1  TO  i-1  DO  Affect (Sta[i,j], Sta[0,j])  END;
	    IntToSup (0, Sta[0,i]);
	    FOR  j := i+1  TO  Order  DO
               Multiply (T1, Sta[i,j], Sta[0,j])
	       END;
	    Insertion;
	    END
	 END
      END
   END Lemme2;

(***************************************************************************)

PROCEDURE InitStates (VAR a : MVect);
(* PROCEDURE InitStates (VAR a : MVect; VAR IP; VAR Sta); ??? *)
   (*  Initialise la matrice carre Sta. La matrice Sta est  *)
   (*  d'ordre egal a l'ordre du generateur. Elle contient  *)
   (*  un systeme de generateurs pour le groupe d'etats     *)
   (*  considere.                                           *)
   VAR
      i, i1, j, k : MDim;
      l, O8 : BDim;   (* O8 devrait etre elimine ?? RS *)
      x     : LONGREAL;
      equal : BOOLEAN;
   BEGIN
   IF  Order > NormalG^.Maxt THEN O8 := NormalG^.Maxt ELSE O8 := Order END;
   IF LatType = Recurrent THEN 
      GCD (aSI[Order], mSI, T1); 
      IF  Negative(T1)  THEN  ChangeSign (T1, T1)  END;
      IntToSup (1, T2)
      END;
   IF (LatType = Full) OR (LatType = PrimePower) OR Equal (T1, T2)  THEN
      FOR  i := 1  TO  Order  DO        
	 FOR  j := 1  TO  Order  DO
	    IF  i # j  THEN
               IntToSup (0, Sta[i,j])
	    ELSE
	       IntToSup (1, Sta[i,j])
	       END
	    END;
	 IP[i] := TRUE;
	 END;
      (*  Calcul de lgVolDual2  *)
      lgVolDual2[1] := lgm2;
      FOR  l :=  2  TO  O8  DO
	 lgVolDual2[l] := lgVolDual2[l-1] + lgm2
	 END;
(* RS ?? Pourquoi pas  FOR  l := O8 + 1  TO  NormalG^.Maxt  DO ??? *)
      FOR  l := VAL (INTEGER, Order) + 1  TO  NormalG^.Maxt  DO
	 lgVolDual2[l] := lgVolDual2[l-1]
	 END
   ELSE
      IF  LatType = Orbit  THEN
	 IntToSup (0, Sta[0,Order]);
	 FOR  i := 1  TO  Order  DO
	    Multiply (aSI[i], InSta[Order+1-i], InSta[0]);
	    Add (InSta[0], Sta[0,Order], Sta[0,Order])
	    END;
	 Subtract (Sta[0,Order], InSta[Order], Sta[0,Order]); 
	 FOR  i := 1  TO  Order-1  DO
	    Subtract (InSta[i+1], InSta[i], Sta[0,i])
	    END
      ELSIF  LatType = Recurrent  THEN
	 LIToMScal (Exposant * Order * NumDigits (mSI)+1, e);
	 MPowerPolyMod (a, Order, e, xi);
	 MScalToSup (xi[Order-1], Sta[0,1]);
	 FOR  i := 2  TO  Order  DO
	    (* Multiplier xi par X et reduire mod X^k - a1 X^{k-1} - .... *)
	    MAffect (xi[Order-1], xi[Order]);
	    FOR  i1 := 1  TO  Order-1  DO
	       (*  Coeff. de X^{Order-i1}.  *)
	       MAffect (xi[Order-i1-1], xi[Order-i1]);
	       MProdModm (xi[Order], a[i1], xi[Order-i1-1]);
	       MAdd (xi[Order-i1-1], xi[Order-i1], xi[Order-i1])
	       END;
	    (*  Coeff. constant.  *)
	    MProdModm (xi[Order], a[Order], xi[0]);
	    MScalToSup (xi[Order-1], Sta[0,i]);
	    END
	 END;
      FOR  i := 1  TO  Order  DO
	 FOR  j := 1  TO  Order  DO  IntToSup (0, Sta[i,j])  END;
	 IP[i] := FALSE;
	 Affect (Sta[0,i], Sta[i,0])
	 END;
      Insertion;
      FOR  k := 2  TO  Order  DO
	 (* On passe a l'etat suivant.                                    *)
	 FOR  j := 1  TO  Order-1  DO  Affect (Sta[j+1,0], Sta[0,j])  END;
	 IntToSup(0, Sta[0,Order]);
	 FOR  i := 1  TO  Order  DO
	    Multiply (aSI[i], Sta[Order-i+1,0], T1);
	    Add (T1, Sta[0,Order], Sta[0,Order])
	    END;
	 Modulo(Sta[0,Order], mSI, Sta[0,Order]);
	 (* On memorise l'etat suivant.                                   *)
	 FOR  i := 1  TO  Order-1  DO  Exchange (Sta[i,0], Sta[i+1,0])  END;
	 Affect(Sta[0,Order], Sta[Order,0]);
	 Insertion
	 END;
      Lemme2;
      (*  Calcul de lgVolDual2  *)
      IF  IP[1]  THEN  
	 lgVolDual2[1] := 2.0 * Lg (DivideLR (mSI, Sta[1,1], equal))
      ELSE
	 lgVolDual2[1] := 0.0
	 END;
      FOR  l := 2  TO  O8  DO
	 IF  IP[l]  THEN
	    x := DivideLR(mSI, Sta[l,l], equal);
	    lgVolDual2[l] := lgVolDual2[l-1] + 2.0 * Lg(x)
	 ELSE
	    lgVolDual2[l] := lgVolDual2[l-1]
	    END
 	 END;
      FOR  l := VAL (INTEGER, Order) + 1  TO  NormalG^.Maxt  DO
	 lgVolDual2[l] := lgVolDual2[l-1]
	 END
      END
   END InitStates;

(***************************************************************************)

PROCEDURE BuildBasis (B : Basis; VAR a : MVect; d : BDim);
   (*  La base est construite en dimension d.  *)
   VAR
      i, j, j1 : MDim;
      dk       : INTEGER;   (* Minimum de d et Order. *)
   BEGIN
   InitStates (a);
   dk := d; IF  dk > VAL (INTEGER, Order)  THEN  dk := Order  END;
   WITH  B^  DO
      SISquares := (NumDigits (mSI) > 33);
      FOR  i := 1  TO  VAL (MDim, dk)  DO
	 IF  IP[i]  THEN
	    FOR  j := 1  TO  VAL (MDim, dk)  DO
	       SupToBScal (Sta[i,j], V[i,j])
	       END
	 ELSE
	    FOR  j := 1  TO  VAL(MDim, dk)  DO
	       IF  i # j  THEN
		  BAffect (BZero, V[i,j])
	       ELSE
		  SupToBScal (mSI, V[i,j])
		  END 
	       END
	    END
	 END;
      FOR  i := 1  TO  VAL (MDim, dk)  DO
	 BDivideRound (mB, V[i,i], W[i,i]);
	 FOR  j := i-1  TO  1  BY -1  DO
	    BAffect (BZero, W[i,j]);
	    FOR  j1 := j+1  TO  i  DO
	       BMultiply (V[j,j1], W[i,j1], W[i,0]);
	       BAdd (W[i,0], W[i,j], W[i,j])
	       END;
	    BChangeSign (W[i,j]);
	    BDivideRound (W[i,j], V[j,j], W[i,j])
	    END;
	 FOR j := i+1  TO  VAL (MDim, dk) DO  BAffect (BZero, W[i,j])  END
	 END;
      Dim := dk
      END;
   IF  d > Order  THEN
      FOR i := Order+1 TO VAL (MDim, d)  DO  IncDimBasis (B)  END
      END
   END BuildBasis;

(***************************************************************************)

PROCEDURE BuildLaBasis
   (B : Basis;   VAR a : MVect;   VAR I : BVect; n, MaxDim : BDim);
   VAR
      i, i1, i2, j, j1, ord : BDim;
   BEGIN
   InitStates(a);   IMax := MaxDim;

   (*  Construction d'un systeme generateur modulo m.                      *)
   FOR  j := 1 TO MaxDim DO
      BScalToMScal (I[j], e);
      MPowerPolyMod (a, Order, e, xi);
      FOR  j1 := 1  TO  Order  DO
	 MScalToSup (xi[j1-1], WSI[0,j1])
	 END;
      ord := 0;
      FOR  i := 1  TO  Order  DO 
	 IF  IP[i]  THEN
	    INC (ord);
	    IntToSup (0, WSI[ord,j]);
	    FOR  j1 := 1  TO  Order  DO
	       Multiply (Sta[i,j1], WSI[0,j1], T1);
	       Add (T1, WSI[ord,j], WSI[ord,j])
	       END
	    END
	 END
      END;

   (*  `Triangulation' modulo m.                                           *)
   FOR  j := 1  TO  MaxDim  DO
      FOR  i := 1  TO  ord  DO  Modulo (WSI[i,j], mSI, WSI[i,j])  END;         
      i1 := 1;
      WHILE  i1 < ord  DO
	 WHILE  (Zero(WSI[i1,j])) AND (i1<ord)  DO  INC(i1)  END;  
	 IF  i1<ord  THEN
	    i2 := i1 + 1;
	    WHILE  (Zero(WSI[i2,j])) AND (i2<ord)  DO  INC(i2)  END;
	    IF  NOT Zero(WSI[i2,j])  THEN
	       Euclide (WSI[i1,j], WSI[i2,j], T1, T2, T3, T4, WSI[i2,j]);
	       IntToSup (0, WSI[i1,j]);
	       FOR  j1 := j+1  TO  MaxDim  DO
		  Multiply (T1, WSI[i1,j1], T5);
		  Multiply (T2, WSI[i2,j1], T6);
                  Multiply (T3, WSI[i1,j1], T7);
                  Multiply (T4, WSI[i2,j1], T8);
		  Add (T5, T6, WSI[i2,j1]);
                  Modulo (WSI[i2,j1], mSI, WSI[i2,j1]);
		  Add (T7, T8, WSI[i1,j1]);
                  Modulo (WSI[i1,j1], mSI, WSI[i1,j1])
		  END
	    ELSE
	       FOR j1 := j TO MaxDim DO Exchange (WSI[i1,j1], WSI[i2,j1]) END
	       END;
	    i1 := i2
	    END
	 END;
      IF  Zero (WSI[ord,j])  THEN
	FOR  j1 := 1  TO  MaxDim  DO
	   IF  j1 # j  THEN
	      IntToSup (0, VSI[j,j1])
	   ELSE
	      Affect (mSI, VSI[j,j1])
	      END
	   END
      ELSE
	 Euclide (WSI[ord,j], mSI, T1, T2, T3, T4, VSI[j,j]);
	 FOR  j1 := 1  TO  j-1  DO  IntToSup (0, VSI[j,j1])  END;
	 FOR  j1 := j+1  TO  MaxDim  DO
	    Multiply (T1, WSI[ord,j1], T2);
	    Modulo (T2, mSI, VSI[j,j1])
	    END;
	 Quotient (mSI, VSI[j,j], T1);
	 FOR  j1 := j+1  TO  MaxDim  DO
	    Multiply (T1, WSI[ord,j1], WSI[ord,j1]);
            Modulo (WSI[ord,j1], mSI, WSI[ord,j1])
	    END
	 END
      END;

   (*  Calcul du m-dual de VSI. Le resultat est place en WSI.             *) 
   FOR  i := 1  TO  MaxDim  DO
      FOR  j := i+1  TO  MaxDim  DO  IntToSup (0, WSI[i,j])  END;
      Quotient(mSI, VSI[i,i], WSI[i,i]);
      FOR  j := i-1  TO  1  BY  -1  DO
	 IntToSup(0, WSI[i,j]);
	 FOR  j1 := j+1  TO  i  DO
	    Multiply(VSI[j,j1], WSI[i,j1], T1);
	    Add(T1, WSI[i,j], WSI[i,j])
	    END;
	 ChangeSign(WSI[i,j], WSI[i,j]);
	 Quotient(WSI[i,j], VSI[j,j], WSI[i,j])
	 END
      END;

   (* Construire la base de dimension 1 *)
   WITH B^ DO
      SupToBScal(VSI[1,1], V[1,1]);
      SupToBScal(WSI[1,1], W[1,1]);
      Dim := 1;
      VVLR[1] := -1.0;   WWLR[1] := -1.0;
      IntToSup(-1, VVSI[1]); IntToSup(-1, WWSI[1])
      END;
   FOR i := 2 TO n DO IncDimLaBasis (B) END;
   END BuildLaBasis;

(**************************************************************************)

PROCEDURE InitOut ();
   (* ecrit 2*Order - 1 vecteurs output successifs d'un generateur Nied *)
   (* dans les colonnes 1,...,2*Order - 1 de VSI                        *)
   BEGIN
   END InitOut;

(**************************************************************************)

PROCEDURE BuildVectLaBasis
   (B : Basis;   VAR a : MVect;   VAR I : BVect; n, MaxDim : BDim);
   VAR
      i, i1, i2, j, j1, l, in_co : BDim;
   BEGIN
   IMax := MaxDim;

   (*  Construction d'un systeme generateur modulo m.                      *)
   in_co := 0;
   FOR  j := 1 TO MaxDim DO
      BScalToMScal (I[j], e);
      MPowerPolyMod (a, Order, e, xi);
      FOR  j1 := 0  TO  Order-1  DO
         MScalToSup (xi[j1], WSI[0,j1])
         END;
      FOR  l := 1  TO  32  DO
         IF  l IN MIC[j]  THEN
            INC (in_co);
            FOR  i := 1  TO  Order  DO
               IntToSup (0, WSI[i,in_co]);
               FOR  j1 := 0  TO  Order-1  DO
                  Multiply (WSI[0,j1], VSI[l,i+j1], T1);
                  Add (T1, WSI[i,in_co], WSI[i,in_co])
                  END
               END
            END
         END
      END;

   (*  `Triangulation' modulo m.                                           *)
   FOR  j := 1  TO  MaxDim  DO
      FOR  i := 1  TO  Order  DO  Modulo (WSI[i,j], mSI, WSI[i,j])  END;
      i1 := 1;
      WHILE  i1 < Order  DO
         WHILE  (Zero (WSI[i1,j])) AND (i1 < Order)  DO  INC (i1)  END;
         IF  i1 < Order  THEN
            i2 := i1 + 1;
            WHILE  (Zero (WSI[i2,j])) AND (i2 < Order)  DO  INC(i2)  END;
            IF  NOT Zero(WSI[i2,j])  THEN
               Euclide (WSI[i1,j], WSI[i2,j], T1, T2, T3, T4, WSI[i2,j]);
               IntToSup (0, WSI[i1,j]);
               FOR  j1 := j+1  TO  MaxDim  DO
                  Multiply (T1, WSI[i1,j1], T5);
                  Multiply (T2, WSI[i2,j1], T6);
                  Multiply (T3, WSI[i1,j1], T7);
                  Multiply (T4, WSI[i2,j1], T8);
                  Add (T5, T6, WSI[i2,j1]);
                  Modulo (WSI[i2,j1], mSI, WSI[i2,j1]);
                  Add (T7, T8, WSI[i1,j1]);
                  Modulo (WSI[i1,j1], mSI, WSI[i1,j1])
                  END
            ELSE
               FOR j1 := j TO MaxDim DO Exchange (WSI[i1,j1], WSI[i2,j1]) END
               END;
            i1 := i2
            END
         END;
      IF  Zero (WSI[Order,j])  THEN
        FOR  j1 := 1  TO  MaxDim  DO
           IF  j1 # j  THEN
              IntToSup (0, VSI[j,j1])
           ELSE
              Affect (mSI, VSI[j,j1])
              END
           END
      ELSE
         Euclide (WSI[Order,j], mSI, T1, T2, T3, T4, VSI[j,j]);
         FOR  j1 := 1  TO  j-1  DO  IntToSup (0, VSI[j,j1])  END;
         FOR  j1 := j+1  TO  MaxDim  DO
            Multiply (T1, WSI[Order,j1], T2);
            Modulo (T2, mSI, VSI[j,j1])
            END;
         Quotient (mSI, VSI[j,j], T1);
         FOR  j1 := j+1  TO  MaxDim  DO
            Multiply (T1, WSI[Order,j1], WSI[Order,j1]);
            Modulo (WSI[Order,j1], mSI, WSI[Order,j1])
            END
         END
      END;

   (*  Calcul du m-dual de VSI. Le resultat est place en WSI.             *)
   FOR  i := 1  TO  MaxDim  DO
      FOR  j := i+1  TO  MaxDim  DO  IntToSup (0, WSI[i,j])  END;
      Quotient(mSI, VSI[i,i], WSI[i,i]);
      FOR  j := i-1  TO  1  BY  -1  DO
         IntToSup(0, WSI[i,j]);
         FOR  j1 := j+1  TO  i  DO
            Multiply(VSI[j,j1], WSI[i,j1], T1);
            Add(T1, WSI[i,j], WSI[i,j])
            END;
         ChangeSign(WSI[i,j], WSI[i,j]);
         Quotient(WSI[i,j], VSI[j,j], WSI[i,j])
         END
      END;

   (* Construire la base de dimension 1 *)
   WITH B^ DO
      SupToBScal(VSI[1,1], V[1,1]);
      SupToBScal(WSI[1,1], W[1,1]);
      Dim := 1;
      VVLR[1] := -1.0;   WWLR[1] := -1.0;
      IntToSup(-1, VVSI[1]); IntToSup(-1, WWSI[1])
      END;
   FOR i := 2 TO n DO IncDimLaBasis (B) END;
   END BuildVectLaBasis;

(**************************************************************************)

PROCEDURE IncDimLaBasis (B : Basis);
   VAR
      i, i1, j : BDim;
   BEGIN
   WITH B^ DO
      IF Dim >= IMax THEN
         WriteString(' Dimension of the basis is too big.'); WriteLn;
         WriteString(' (Dim > Number of lacunary indices.'); WriteLn;
         HALT
         END;

      FOR  i := 1  TO  Dim  DO
         (*  Vi -> VSI0.  *)
         FOR  j := 1  TO  Dim  DO
            BScalToSup(V[i,j], VSI[0,j])
            END;
         IntToSup(0, VSI[i,0]);
         FOR  i1 := 1  TO  Dim  DO
            BASISSI.BProdScal(VSI[0], WSI[i1], Dim, WSI[i1,0]);
            Quotient(WSI[i1,0], mSI, WSI[i1,0]);
            Multiply(WSI[i1,0], VSI[i1,Dim+1], T1);
            Add(T1, VSI[i,0], VSI[i,0])
            END;
         Modulo (VSI[i,0], mSI, VSI[i,0]);
         SupToBScal(VSI[i,0], V[i,Dim+1])
         END;

      FOR  j := 1  TO  Dim  DO
         BAffect (BZero, V[Dim+1,j])
         END;
      SupToBScal (VSI[Dim+1,Dim+1], V[Dim+1,Dim+1]);

      FOR  i := 1  TO  Dim  DO  BAffect (BZero, W[i,Dim+1]) END;
      FOR  j := 1  TO  Dim  DO
         IntToSup(0, WSI[0,j]);
         FOR  i := 1  TO  Dim  DO
            BScalToSup(W[i,j], T1);
            Multiply(VSI[i,0], T1, T1);
            Add(T1, WSI[0,j], WSI[0,j])
            END;
         ChangeSign(WSI[0,j], WSI[0,j]);
         Quotient(WSI[0,j], VSI[Dim+1,Dim+1], WSI[0,j]);
         SupToBScal(WSI[0,j], W[Dim+1,j])
         END;
      Quotient (mSI, VSI[Dim+1,Dim+1], T1);
      SupToBScal (T1, W[Dim+1, Dim+1]);

      INC(Dim);

      IF  SISquares  THEN
         FOR  i := 1  TO  Dim  DO
            BASISSI.BSetNeg (VVSI[i]);
            BASISSI.BSetNeg (WWSI[i])
            END
      ELSE
         FOR  i := 1  TO  Dim  DO
            VVLR[i] := -1.0;
            WWLR[i] := -1.0
            END
         END
      END
   END IncDimLaBasis;

(**************************************************************************)

PROCEDURE PrintSkipMult (VAR a : MVect);
   BEGIN
   WriteLn;   WriteString ( 'Vecteur multiplicateurs:' );
   MWriteVect (a, Order);   WriteLn;
   END PrintSkipMult;

(**************************************************************************)

PROCEDURE PrintHeadRES (T : CriterionType; MaxDim : BDim; Verif : VerifyType);
   VAR
      t : BDim;
   BEGIN
   WriteString ("RESULTS for Beyer and/or Spectral tests, ");
   IF Verif = Verify2 THEN
      WriteString ("with verification (REDBAS2).")
   ELSIF Verif = Verify3 THEN
      WriteString ("with verification (REDBAS3).")
   ELSE
      WriteString ("without verification (using REDBAS).")
      END; 
   WriteLn;  WriteLn;
   IF Lacunary THEN
      WriteString (' Lacunary Indices: ');   WriteLn;
      FOR t := 1 TO MaxDim DO
	 BScalToSup (LacI[t], T4);
	 WriteString ('  ');  WriteSup (T4, 10, 70);
	 IF t MOD 3 = 0 THEN  WriteLn END
	 END;
      END;
   WriteLn;
   WriteString ('    t     ');
   IF (T = Spectral) OR (T = BeyerSpectral) THEN
      WriteString ('      d_t     ')
      END;
   IF (T = SpectralL1) THEN
      WriteString ('      N_t          N_t^*    ')
      END;
   IF (T = Beyer) OR (T = BeyerSpectral) THEN
      WriteString ('      q_t     ')
      END;
   IF (T # Beyer) THEN
      WriteString ('      S_t     ')
      END;
   WriteString (' Total CPU (sec)');
   WriteLn;   WriteString (' -------------------------------------------');
   WriteString ('------------------------');   WriteLn;
   END PrintHeadRES;

(**************************************************************************)

PROCEDURE PrintHeadTEX (T : CriterionType; MaxDim : BDim;  Verif : VerifyType);
   VAR
      t : BDim;
   BEGIN
   WriteLn;
   WriteString ("RESULTS for Beyer and/or Spectral tests, ");
   IF Verif = Verify2 THEN
      WriteString ("with verification (REDBAS2).\\")
   ELSIF Verif = Verify3 THEN
      WriteString ("with verification (REDBAS3).\\")
   ELSE
      WriteString ("without verification (using REDBAS).\\")
      END; 
   WriteLn;  WriteLn;
   IF Lacunary THEN
      WriteString (' Lacunary Indices:\\ ');   WriteLn;
      FOR t := 1 TO MaxDim DO
	 BScalToSup (LacI[t], T4);
	 WriteString ('  ');  WriteSup (T4, 10, 70);
	 IF (t MOD 4 = 0) THEN  WriteString ("\\"); WriteLn END
	 END;
      WriteLn
      END;
   WriteString ('\begin {tabular}{|rlllr|}');  WriteLn;
   WriteString ('\hline');  WriteLn;
   WriteString (' &&&&  cumulative \\');   WriteLn;
   WriteString ('   $t$ & ');
   IF (T = Spectral) OR (T = BeyerSpectral) THEN
      WriteString ('     $d_t$  & ')
      END;
   IF (T = Beyer) OR (T = BeyerSpectral) THEN
      WriteString ('     $q_t$  & ')
      END;
   IF (T = SpectralL1) THEN
      WriteString ('     $N_t$   &   $N_t^*$  & ')
      END;
   IF (T # Beyer) THEN
      WriteString ('     $S_t$  & ')
      END;
   WriteString (' cpu (sec)\\');   WriteLn;
   WriteString ('\hline');   WriteLn;
   END PrintHeadTEX;

(***************************************************************************)

PROCEDURE PrintLine (T : CriterionType;  t : CARDINAL);
   BEGIN
   WriteInt (t, 5);   
   IF LaTeX THEN  WriteString ( '  & ' )  ELSE  WriteString ( '    ' ) END;
   IF (T = Spectral) OR (T = BeyerSpectral) THEN
      WriteLR ( Sqrt ( D2[t] ), 12, 5, 4);
      IF LaTeX THEN  WriteString ( ' &' )  ELSE  WriteString ( '  ' ) END;
      END;
   IF (T = Beyer) OR (T = BeyerSpectral) THEN
      WriteLR (Sqrt (Q2[t]), 12, 5, 4);
      IF LaTeX THEN  WriteString ( ' &' )  ELSE  WriteString ( '  ' ) END;
      END;
   IF ((T = Spectral) OR (T = BeyerSpectral)) THEN
      IF (t <= NormalG^.Maxt) THEN  
         IF InvertCrit THEN
            WriteLR (1.0 / Sqrt (S2[t]), 12, 5, 4)  
         ELSE
            WriteLR (Sqrt (S2[t]), 12, 5, 4)  
            END
      ELSE  WriteString ("            ")  END;
      IF LaTeX THEN  WriteString ( ' &' )  ELSE  WriteString ( '  ' ) END;
      END;
(* temporaire pour comparer   WriteLR (ValChrono (chrono, sec), 10, 2, 1); *) 
   IF LaTeX THEN  WriteString ( ' \\' )  END;
   WriteLn;
   END PrintLine;

(***************************************************************************)

PROCEDURE PrintLineL1 (T : CriterionType;  t : CARDINAL);
   (* ?? Imprime resultats quand NormType = L1Norm ?? *)
   VAR
      x : LONGREAL;
   BEGIN
   WriteInt (t, 5);
   IF LaTeX THEN  WriteString ( '  & ' )  ELSE  WriteString ( '    ' ) END;
   WriteLR (Bas^.VVLR[1], 12, 1, 4);
   IF LaTeX THEN  WriteString ( ' &' )  ELSE  WriteString ( '  ' ) END;
   x := TruncLR (Pow (Factorielle (t) * Bas^.mLR, 1.0 / IToLR (t)));
   WriteLR (x, 12, 1, 4);  
   IF LaTeX THEN  WriteString ( ' &' )  ELSE  WriteString ( '  ' ) END;
   IF InvertCrit THEN
      WriteLR (1.0 / S2[t], 12, 5, 4)  
   ELSE
      WriteLR (S2[t], 12, 5, 4)  
      END;
   IF LaTeX THEN  WriteString ( ' &' )  ELSE  WriteString ( '  ' ) END;
   WriteLR (ValChrono (chrono, sec), 10, 2, 1);  
   IF LaTeX THEN  WriteString ( ' \\' )  END;
   WriteLn;
   END PrintLineL1;

(***************************************************************************)

PROCEDURE BeyerTest (VAR a : MVect;  MaxDim : BDim;  Verif : VerifyType);
   VAR
      i : BDim;
      VerifOK : BOOLEAN;
   BEGIN
   WITH Bas^ DO
      Dualize (Bas);
      PreRedDieter (Bas, 0);
      Dualize (Bas);
      WHILE Dim < MaxDim DO
	 IF Lacunary THEN IncDimLaBasis (Bas) ELSE IncDimBasis (Bas) END;
	 IF ReductMinkowski (Bas, 0) THEN
	    IF  Verif = Verify2 THEN 
               VerifOK := REDBAS2.VerifMinkowski (Bas, 0)
	    ELSIF  Verif = Verify3 THEN 
               VerifOK := REDBAS3.VerifMinkowski (Bas, 0)
            ELSE
               VerifOK := TRUE;
               END;
            IF (NOT VerifOK) THEN
               IF print THEN
		  WriteString ('MRG.BeyerTest: Verif: ');
		  WriteString ('Basis was not reduced.');
		  WriteLn;
                  END;
	       END;
	    IF VVLR[1] < 0.0 THEN
	       VVLR[1] := BProdScalLR (V[1], V[1], Dim) END;
	    IF VVLR[Dim] < 0.0 THEN
	       VVLR[Dim] := BProdScalLR (V[Dim], V[Dim], Dim) END;
	    S2[Dim] := VVLR[1]/VVLR[Dim];
            (* Si on sait deja que ce gen. ne pourra etre retenu,     *)
            (* on le rejette tout de suite et on arrete le test.      *)
	    IF (MaxAllDim AND (S2 [Dim] < Mins2 [MaxDim])) OR
                  (S2 [Dim] < Mins2 [Dim])  THEN
               TestCompleted := FALSE;   S2 [Dim] := 0.0;  RETURN
               END;
	    IF print THEN PrintLine (Beyer, Dim); END;
	 ELSE
	    IF print THEN PrintSkipMult (a); END;
	    TestCompleted := FALSE;   S2 [Dim] := 0.0;  RETURN
	    END
	 END
      END;
   TestCompleted := TRUE;
   END BeyerTest;

(**************************************************************************)

PROCEDURE SpectralTest (VAR a : MVect;  MaxDim : BDim;  Verif : VerifyType);
   VAR
      VerifOK : BOOLEAN;
      z       : VectLI;
      lgvv1, TempLR : LONGREAL;
   BEGIN
   WITH Bas^ DO
      PreRedDieter (Bas, 0);
      WHILE Dim < MaxDim DO
	 IF Lacunary THEN IncDimLaBasis (Bas) ELSE IncDimBasis (Bas) END;
	 IF DualLattice THEN  Dualize (Bas)  END;
	 IF ShortestVector (Bas) THEN
	    IF  Verif = Verify2 THEN 
               VerifOK := REDBAS2.VerifShortest (Bas)
	    ELSIF  Verif = Verify3 THEN 
               VerifOK := REDBAS3.VerifShortest (Bas, 0, (Dim DIV 2), z)
            ELSE
               VerifOK := TRUE;
               END;
	    IF (NOT VerifOK) THEN
	       IF print THEN
	          WriteString ('MRG.SpectralTest: Verif: ');
                  WriteString ('Vector was not shortest.');
                  WriteLn;
                  END
	       END;

            (* Calcul de D2. *)
            IF  SISquares  THEN
               IF  Negative (VVSI[1]) AND (Norm = L2Norm) THEN
                  BProdScalSI (V[1], V[1], Dim, VVSI[1])
                  END;
               SupToLongReal (VVSI[1], TempLR);
               IF Dim <= NormalG^.Maxt THEN
                  (*  Calcul du logarithme (base 2) de ||v1||^2.        *)
	          lgvv1 := Log2 (VVSI[1])
                  END
	    ELSE
               (* Pour Norm # L2Norm, suppose que VVLR est a jour.      *)
	       IF (VVLR[1] < 0.0) (* AND (Norm = L2Norm) *) THEN
	          VVLR[1] := BProdScalLR (V[1], V[1], Dim)
	          END;
               TempLR := VVLR[1];
               IF  Dim <= NormalG^.Maxt  THEN
                  (*  Calcul du logarithme (base 2) de ||v1||^2.        *)
	          lgvv1 := Lg (VVLR[1])
	          END
               END;
            IF (Norm = L2Norm) THEN  
               D2[Dim] := 1.0 / TempLR
            ELSE
               D2[Dim] := VVLR[1]
               END;
            IF  Dim <= NormalG^.Maxt  THEN
	       (* Calcul de S2.                                         *)
               IF Norm = L2Norm THEN
                  S2[Dim] := Pow (2.0, lgvv1 - lgVolDual2[Dim] / IToLR (Dim))
			     / (NormalG^.Gamma [Dim])
               ELSIF Norm = L1Norm THEN
                  TempLR :=  Pow (2.0, (lgVolDual2[Dim] / 2.0 
                             + NormalG^.Gamma [Dim]) / IToLR (Dim));
                  S2[Dim] := Pow (2.0, lgvv1) / TruncLR (TempLR);
               ELSE
                  S2[Dim] := 0.0;
                  END;
               (* Si on sait deja que ce gen. ne pourra etre retenu,     *)
               (* on le rejette tout de suite et on arrete le test.      *)
	       IF (MaxAllDim AND (S2 [Dim] < Mins2 [MaxDim])) OR
                     (S2 [Dim] < Mins2 [Dim])  THEN
		  TestCompleted := FALSE;   S2 [Dim] := 0.0;  RETURN
                  END
	       END;
	    IF print THEN 	
               IF Norm = L2Norm THEN
                  PrintLine (Spectral, Dim)
               ELSE
                  PrintLineL1 (Spectral, Dim);
                  END;
               END;
            IF DualLattice THEN  Dualize (Bas)  END;
	 ELSE
	    IF print THEN PrintSkipMult (a); END;
	    TestCompleted := FALSE;   S2[Dim] := 0.0;   RETURN
	    END
	 END
      END;
   TestCompleted := TRUE;
   END SpectralTest;
   
(**************************************************************************)

PROCEDURE BeyerSpectralTest (VAR a : MVect; MaxDim : BDim; Verif: VerifyType);
   VAR
      TempLR, lgvv1 : LONGREAL;
      VerifOK : BOOLEAN;
      z : VectLI;
   BEGIN
   WITH Bas^ DO
      PreRedDieter (Bas, 0);
      WHILE Dim < MaxDim DO
	 IF Lacunary THEN IncDimLaBasis (Bas) ELSE IncDimBasis (Bas) END;
         IF DualLattice THEN  Dualize (Bas)  END;
	 IF ShortestVector (Bas) THEN
	    IF  Verif = Verify2 THEN 
               VerifOK := REDBAS2.VerifShortest (Bas)
	    ELSIF  Verif = Verify3 THEN 
               VerifOK := REDBAS3.VerifShortest (Bas, 0, (Dim DIV 2), z)
            ELSE
               VerifOK := TRUE;
               END;
	    IF (NOT VerifOK) THEN
	       IF print THEN
		  WriteString ('MRG.BeyerSpectralTest: Verif: ');
		  WriteString ('Vector was not shortest.');
		  WriteLn;
		  END;
	       END;

            (* Calcul de D2. *)
            IF  SISquares  THEN
               IF  Negative (VVSI[1])  THEN
                  BProdScalSI (V[1], V[1], Dim, WWSI[1])
                  END;
               SupToLongReal (VVSI[1], TempLR);
               D2[Dim] := 1.0/TempLR;    (* For L_2 Spectral test only. *)
               IF Dim <= NormalG^.Maxt THEN
                  (*  Calcul du logarithme (base 2) de ||v1||^2.        *)
	          lgvv1 := Log2 (VVSI[1])
                  END
	    ELSE
	       IF VVLR[1] < 0.0 THEN
	          VVLR[1] := BProdScalLR (V[1], V[1], Dim)
	          END;
               D2[Dim] := 1.0/VVLR[1];
               IF  Dim <= NormalG^.Maxt  THEN
                  (*  Calcul du logarithme (base 2) de ||v1||^2.        *)
	          lgvv1 := Lg (VVLR[1])
	          END
               END;
            IF  Dim <= NormalG^.Maxt  THEN
	       (* Calcul de S2.                                         *)
	       S2[Dim] := Pow (2.0, lgvv1 - lgVolDual2[Dim] / IToLR(Dim))
                          / (NormalG^.Gamma[Dim]);
               (* Si on sait deja que ce gen. ne pourra etre retenu,     *)
               (* on le rejette tout de suite et on arrete le test.      *)
	       IF (MaxAllDim AND (S2 [Dim] < Mins2 [MaxDim])) OR
                     (S2 [Dim] < Mins2 [Dim])  THEN
		  TestCompleted := FALSE;   S2 [Dim] := 0.0;  RETURN
                  END
	       END;
            IF DualLattice THEN  Dualize (Bas)  END;
	 ELSE
	    IF print THEN PrintSkipMult (a); END;
	    TestCompleted := FALSE;   RETURN
	    END;

	 IF ReductMinkowski (Bas, 0) THEN
	    IF  Verif = Verify2 THEN 
               VerifOK := REDBAS2.VerifMinkowski (Bas, 0)
	    ELSIF  Verif = Verify3 THEN 
               VerifOK := REDBAS3.VerifMinkowski (Bas, 0)
            ELSE
               VerifOK := TRUE;
               END;
            IF (NOT VerifOK) THEN
               IF print THEN
		  WriteString ('MRG.BeyerSpectralTest: Verif: ');
		  WriteString ('Basis was not reduced.');
		  WriteLn; END;
	       END;
	    IF VVLR[1] < 0.0 THEN
	       VVLR[1] := BProdScalLR (V[1], V[1], Dim) END;
	    IF VVLR[Dim] < 0.0 THEN
	       VVLR[Dim] := BProdScalLR (V[Dim], V[Dim], Dim) END;
	    Q2[Dim] := VVLR[1]/VVLR[Dim];
            (* Si on sait deja que ce gen. ne pourra etre retenu,     *)
            (* on le rejette tout de suite et on arrete le test.      *)
	    IF (MaxAllDim AND (Q2 [Dim] < Minq2 [MaxDim])) OR
                  (Q2 [Dim] < Minq2 [Dim])  THEN
               TestCompleted := FALSE;   Q2 [Dim] := 0.0;  RETURN
               END;
	 ELSE  IF print THEN PrintSkipMult ( a ); END;
	    END;
	 IF print THEN PrintLine (BeyerSpectral, Dim); END;
	 END;
      END;
   TestCompleted := TRUE;
   END BeyerSpectralTest;

(**************************************************************************)

PROCEDURE Test
   ( VAR a          : MVect;
     T              : CriterionType;
     FromDim, ToDim : BDim;
     VerifyBB       : VerifyType;
     Out            : OutputType
   );
   VAR
     i: BDim;
   BEGIN
   LaTeX := (Out = CurOutTex);
   PreRedDieterSV   := TRUE;    PreRedLLLRM := FALSE;
   IF FromDim <= Order THEN
      WriteString (' WARNING from MRG.Test:  FromDim should be > Order.');
      WriteLn;
      WriteString (' The program will now reset:  FromDim := Order + 1;');
      WriteLn;  WriteLn;
      END;
   CASE Out OF
      None       : print := FALSE;
    | CurOut     : PrintHeadRES (T, ToDim, VerifyBB);  print := TRUE;
    | CurOutTex  : PrintHeadTEX (T, ToDim, VerifyBB);  print := TRUE;
      END;
   FOR  i := 1  TO  Order DO  MScalToSup (a[i], aSI[i])  END;
   IF NOT Lacunary THEN  
      BuildBasis (Bas, a, FromDim-1)  ;
   ELSE
      BuildLaBasis (Bas, a, LacI, FromDim-1, ToDim)
      END;
   Bas^.Norm := UsedNorm;
   InitChrono (chrono);
   CASE T OF
      Beyer : BeyerTest (a, ToDim, VerifyBB)
    | BeyerSpectral : BeyerSpectralTest (a, ToDim, VerifyBB)
    | Spectral, SpectralL1 : SpectralTest (a, ToDim, VerifyBB)
      END;
   IF print AND (NOT TestCompleted) THEN
      WriteLn;   WriteLn;
      WriteString (' Tests failed in Dimension = ');
      WriteInt (Bas^.Dim, 2);   WriteLn
      END;
   IF LaTeX THEN 
      WriteString ("\hline");  WriteLn;
      WriteString ("\end {tabular}");  WriteLn
      END;
   print := TRUE
   END Test;

(**************************************************************************)

PROCEDURE TestCri
   ( VAR a          : MVect;
     T              : CriterionType;
     FromDim, ToDim : BDim;
     VerifyBB       : VerifyType;
     Out            : OutputType;
     r		    : BDim;
     n		    : INTEGER
   );
   VAR
   	i	    : BDim;
   BEGIN
Error ("TestCri non terminee");
   LaTeX := (Out = CurOutTex);
   PreRedDieterSV   := TRUE;    PreRedLLLRM := FALSE;
   IF FromDim <= Order THEN
      WriteString (' WARNING from MRG.Test:  FromDim should be > Order.');
      WriteLn;
      WriteString (' The program will now reset:  FromDim := Order + 1;');
      WriteLn;  WriteLn;
      END;
   CASE Out OF
      None       : print := FALSE;
    | CurOut     : PrintHeadRES (T, ToDim, VerifyBB);  print := TRUE;
    | CurOutTex  : PrintHeadTEX (T, ToDim, VerifyBB);  print := TRUE;
      END;
   FOR  i := 1  TO  Order DO  MScalToSup (a[i], aSI[i])  END;
   IF NOT Lacunary THEN 
      BuildBasis (Bas, a, FromDim-1)  ;
   ELSE
      BuildLaBasis (Bas, a, LacI, FromDim-1, ToDim)
      END;
   Bas^.Norm := UsedNorm;
   InitChrono (chrono);
   CASE T OF
      Beyer : BeyerTest (a, ToDim, VerifyBB)
    | BeyerSpectral : BeyerSpectralTest (a, ToDim, VerifyBB)
    | Spectral, SpectralL1 : (* CriSpectralTest (a, ToDim, VerifyBB, r, n) *)
      END;
   IF print AND (NOT TestCompleted) THEN
      WriteLn;   WriteLn;
      WriteString (' Tests failed in Dimension = ');
      WriteInt (Bas^.Dim, 2);   WriteLn
      END;
   IF LaTeX THEN 
      WriteString ("\hline");  WriteLn;
      WriteString ("\end {tabular}");  WriteLn
      END;
   print := TRUE
   END TestCri;


(****************************************************************************)

PROCEDURE TestLa
   ( VAR a   : MVect;
     VAR I   : BVect;
     T       : CriterionType;
     FromDim, ToDim : BDim;
     VerifyBB       : VerifyType;
     Out            : OutputType
   );
    BEGIN
    IF  NOT Lacunary  THEN 
       WriteString (" ERROR Call MRG.TestLa while Lacunary = FALSE");  WriteLn
       END;  
    LacI := I;   (* BCopyVect (I, LacI, ToDim);  *)
    Test (a, T, FromDim, ToDim, VerifyBB, Out);
    END TestLa;
    

(****************************************************************************)

PROCEDURE PerMax (VAR a : MVect;   VAR ListmMS1, Listr : Factors) : BOOLEAN;
   BEGIN
   IF IsPrime (Bas^.mSI, 100) THEN
      TestCompleted := TRUE;
      SetFactors (ListmMS1, Listr, Order);
      IF PrimElem (a) THEN  IF MaxPeriod (a) THEN  RETURN TRUE  END  END
   ELSE
      WriteString (" ERROR MRG: Asked for max. period, and m was assumed");
      WriteString ("  to be prime, but it is not.");  WriteLn;
      TestCompleted := FALSE;
      END;
   RETURN FALSE
   END PerMax;

(*************************************************************************)

BEGIN
DualLattice := TRUE;
UsedNorm    := L2Norm;
curmaxMDim  := 0;
curmaxBDim  := 0;
print       := TRUE;
TestCompleted := FALSE;
MaxAllDim   := TRUE;

FOR i := 1 TO BMaxDim DO  
   Minq2 [i] := 0.0;
   Q2 [i]    := 0.0;
   END;

CreateBasis (Bas);
BCreateScal (mB);
Create (mSI, 2);
MCreateScal (e);
Create (T1, 2);  Create (T2, 2);  Create (T3, 2);  Create (T4, 2);
Create (T5, 2);  Create (T6, 2);  Create (T7, 2);  Create (T8, 2);

FOR  l := 0  TO  MMaxDim  DO
   Create (aSI[l], 2);
   Create (InSta[l], 2)
   END;
FOR  l := 0  TO  MMaxDim  DO
   FOR  ll := 0  TO  MMaxDim  DO  Create (Sta[l,ll], 2) END
   END;

CreateNormaliz (NormalG);
END MRG.
