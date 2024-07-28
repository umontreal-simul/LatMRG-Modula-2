(* ndx +, stck +, assgn +, op +, cpydn + *)

IMPLEMENTATION MODULE REDBAS;

IMPORT BASISLR, BASISSI;
FROM Storage  IMPORT ALLOCATE;
FROM SYSTEM   IMPORT ADDRESS;
FROM NUM      IMPORT Sqrt, Round, RoundLR, LIToLR, IToLR, MaxLongIntLR,
                     MaxIntLongReal, TruncLR, Trunc;
FROM MYINOUT  IMPORT WriteString, WriteLn, Error;

FROM SUPINT   IMPORT SuperInteger, Create, Delete, Affect, NumDigits, NumBits;
FROM SUPCONV  IMPORT IntToSup, SupToInt;
FROM SUPARITH IMPORT ShiftLeft, Multiply, ChangeSign, Smaller, Negative,
                     Positive, Zero, Divide, DivideLR;

FROM CONFIG   IMPORT BMaxDim, BDim;
FROM BASIS    IMPORT BScal, BVect, BMatr, BCreateVect, BCreateMatr,
                     BAffect, BProdScalLR, BProdScalSI, BCopyMatr,
                     BL2NormLR, BL1NormLR, BSupNormLR, BL1NormSI, BSupNormSI,
                     BModifVectLR, BModifVectLI, BChangeSignVect,
                     BCopyVect, BZero, BCreateScal,
                     BChangeSign, BModifVect, BDeleteVect, BDeleteMatr;
FROM BASISLR  IMPORT GCD2vect, VectLI;
FROM LATBASIS IMPORT Basis, Permute, UpdateVVWW, SortBasis, WriteBasis;
FROM CONVERT  IMPORT SupToBScal;
FROM NORM     IMPORT NormType;


VAR
   CurMaxDim        : BDim;            (* Maximum dim. that can be treated. *)
                                       (* Value is set by InitREDBAS.       *)
   CountNodes       : LONGINT;         (* Counts the number of nodes in     *)
                                       (* the branch-and-bound tree.        *)
   CountDieter      : LONGINT;         (* Counts nb. of attempts since last *)
                                       (* successful Dieter transformation. *)
   cpt              : LONGINT;         (* Counts nb. of successes in        *)
                                       (* pre-reduction transformations.    *)

   (* Vectors and matrices created by InitREDBAS. *)                      
   VTemp, WTemp     : BMatr;           (*  *)
   Sv               : BASISSI.BVect;   (*  *)
   Y                : BVect;           (* Utilise dans REDDiet              *)
   ZeroVect         : BVect;           (* Vector of zeros.                  *)

   (* Other temporary variables. *)
   BS                 : BScal;
   VVLRTemp, WWLRTemp : BASISLR.BVect;
   S0, S1, S2, S3, S4 : SuperInteger;

   (* Global variables used in the recursive branch-and-bound procedures    *)
   (* Tryz and Tryz0.                                                       *)
   zLI, zshort   : VectLI;
   zLR, N2, DC2  : BASISLR.BVect;
   C0            : BASISLR.BMatr;      (* Choleski matrix of order 0.       *)
   FoundZero     : BOOLEAN;            (* We found the zero vector.         *)
   smaller       : BOOLEAN;            (* We found a smaller vector.        *) 


(**************************************************************************)

PROCEDURE InitREDBAS (MaxDim : BDim);
   VAR
      i  : BDim;
   BEGIN
   IF CurMaxDim > 0 THEN DeleteREDBAS END;
   CurMaxDim := MaxDim;
   IF MaxDim > 0 THEN 
      BCreateMatr (VTemp, 0, MaxDim);  
      BCreateMatr (WTemp, 0, MaxDim);
      BASISSI.BCreateVect (Sv, 0, MaxDim);
      BCreateVect (Y, 0, MaxDim);
      BCreateVect (ZeroVect, 0, MaxDim);
      FOR i := 0 TO MaxDim DO  BAffect (BZero, ZeroVect[i]) END
      END;
   END InitREDBAS;


PROCEDURE DeleteREDBAS;   
   BEGIN
   IF  CurMaxDim > 0 THEN
      BDeleteMatr (VTemp, 0, CurMaxDim);  
      BDeleteMatr (WTemp, 0, CurMaxDim); 
      BASISSI.BDeleteVect (Sv, 0, CurMaxDim);
      BDeleteVect (Y, 0, CurMaxDim);
      BDeleteVect (ZeroVect, 0, CurMaxDim);
      END;
   CurMaxDim := 0;
   END DeleteREDBAS;

PROCEDURE GetMaxDim (): BDim;
   BEGIN
   RETURN CurMaxDim
   END GetMaxDim;

(**************************************************************************)

PROCEDURE PairwiseRedPrimalLR (B : Basis;  i, d : BDim);
   (* Transformation primale T[i] de Dieter (1975), if SISquares = FALSE. *)
   VAR
      j      : BDim;
      q, t0  : LONGREAL;
      qLI    : LONGINT;
   BEGIN
   INC (CountDieter);
   WITH B^ DO
      IF VVLR[i] < 0.0 THEN  VVLR[i] := BProdScalLR (V[i], V[i], Dim) END;
      FOR j := d + 1 TO Dim DO
         IF i # j THEN
            (* Valeur reelle de q qui minimise ||V_j - q V_i||^2.           *)
            (* On prendra ensuite l'entier le plus proche.                  *)
            q := BProdScalLR (V[i], V[j], Dim) / VVLR[i];
            IF  ABS(q) < MaxLongIntLR  THEN
               (* On peut representer q en LONGINT.                         *)
               qLI := Round(q);
               IF qLI # 0 THEN
                  IF VVLR[j] < 0.0 THEN  
                     VVLR[j] := BProdScalLR (V[j], V[j], Dim) 
                     END;
                  BModifVectLI (V[j], V[i], -qLI, Dim);
                  (* Verification.                                          *)
                  t0 := BProdScalLR (V[j], V[j], Dim);
                  IF  t0 < VVLR[j]  THEN
                     (* Le vecteur est vraiment strictement plus court.     *)
                     VVLR[j] := t0;   INC (cpt);   CountDieter := 0;
                     XX[i] := FALSE;  XX[j] := FALSE;
                     BModifVectLI (W[i], W[j], qLI, Dim);
                     WWLR[i] := -1.0
                  ELSE
                     BModifVectLI (V[j], V[i], qLI, Dim)
                     END
                  END;
            ELSE
               (* On represente q en LONGREAL.                             *)
               IF  ABS(q) < MaxIntLongReal  THEN  q := TruncLR(q) END;
               BModifVectLR (V[j], V[i], -q, Dim);
               BModifVectLR (W[i], W[j], q, Dim);
               VVLR[j] := -1.0;   WWLR[i] := -1.0;
               INC (cpt);   CountDieter := 0;
               XX[i] := FALSE;  XX[j] := FALSE
               END
            END
         END
      END;
   END PairwiseRedPrimalLR;


PROCEDURE PairwiseRedPrimalSI (B : Basis;  i, d : BDim);
   (* Utilise dans le cas SISquares.  *)
   VAR
      j : BDim;
   BEGIN
   INC (CountDieter);
   WITH B^ DO
      IF  VVSI[i]^.Negative  THEN
         BProdScalSI (V[i], V[i], Dim, VVSI[i])
         END;
      FOR  j := d + 1 TO Dim  DO
         IF i # j THEN
            BProdScalSI (V[i], V[j], Dim, S3);
            BASISSI.BDivideRound (S3, VVSI[i], S3);
            IF  NOT Zero (S3)  THEN
               (* V[j] - S3 * V[i] est strictement plus court que V[j]:  *)
               (* On modifie V[j] et W[i].                               *)
               SupToBScal(S3, BS);
               BModifVect(W[i], W[j], BS, Dim);
               BChangeSign (BS);
               BModifVect (V[j], V[i], BS, Dim);
               WWSI[i]^.Negative := TRUE;   VVSI[j]^.Negative := TRUE;
               INC (cpt);   CountDieter := 0
               END
            END
         END
      END
   END PairwiseRedPrimalSI;


PROCEDURE PairwiseRedPrimal (B : Basis;  i, d : BDim);
   BEGIN
   WITH  B^  DO
      IF  SISquares  THEN
         PairwiseRedPrimalSI (B, i, d)
      ELSE
         PairwiseRedPrimalLR (B, i, d)
         END
      END
   END PairwiseRedPrimal;


PROCEDURE PairwiseRedDualLR (B : Basis;  i : BDim);
   VAR
      j         : BDim;
      q         : BASISLR.BVect;
      t0, UnSurWWLR : LONGREAL;
   BEGIN
   INC (CountDieter);
   WITH B^ DO
      IF VVLR[i] < 0.0 THEN  VVLR[i] := BProdScalLR (V[i], V[i], Dim)  END;
      IF WWLR[i] < 0.0 THEN  WWLR[i] := BProdScalLR (W[i], W[i], Dim)  END;
      UnSurWWLR := 1.0 / WWLR[i];
      (* Le vecteur presume plus court sera V[0] = V[i] + sum_j q[j] V[j].  *)
      BCopyVect (V[i], V[0], Dim);
      FOR j := 1 TO Dim DO
         IF i # j THEN
            q[j] := RoundLR (BProdScalLR (W[i], W[j], Dim) * UnSurWWLR);
            IF q[j] # 0.0 THEN  BModifVectLR (V[0], V[j], q[j], Dim)  END
            END
         END;
      (* On verifie si ||V[0]|| < ||V[i]||.                                 *)
      t0 := BProdScalLR (V[0], V[0], Dim);
      IF  t0 <  VVLR[i]  THEN
         (* Vraiment plus court. Met V[0] dans V[i] et met a jour le dual.  *)
         CountDieter := 0;  INC(cpt);   XX[i] := FALSE;
         BCopyVect(V[0], V[i], Dim);    VVLR[i] := t0;
         FOR j := 1 TO Dim DO
            IF (i # j) AND (q[j] # 0.0) THEN
               BModifVectLR (W[j], W[i], -q[j], Dim);
               XX[j] := FALSE;   WWLR[j] := -1.0
               END
            END
         END
      END;
   END PairwiseRedDualLR;


PROCEDURE PairwiseRedDualSI (B : Basis;  i : BDim);
   (* Used when SISquares = TRUE.  *)
   VAR
      j : BDim;
   BEGIN
   INC (CountDieter);
   WITH B^ DO
      IF VVSI[i]^.Negative THEN BProdScalSI (V[i], V[i], Dim, VVSI[i]) END;
      IF WWSI[i]^.Negative THEN BProdScalSI (W[i], W[i], Dim, WWSI[i]) END;
      BCopyVect (V[i], V[0], Dim);
      FOR j := 1 TO Dim DO
         IF i # j THEN
            BProdScalSI (W[i], W[j], Dim, S1);
            BASISSI.BDivideRound (S1, WWSI[i], Sv[j]);
            IF NOT Zero (Sv[j]) THEN
               SupToBScal (Sv[j], BS);
               BModifVect (V[0], V[j], BS, Dim)
               END
            END
         END;
      BProdScalSI (V[0], V[0], Dim, S2);
      IF  Smaller (S2, VVSI[i])  THEN
         INC(cpt);   CountDieter := 0;
         BCopyVect(V[0], V[i], Dim);  Affect(S2, VVSI[i]);
         FOR j := 1 TO Dim DO
            IF (i # j) AND (NOT Zero (Sv[j]))  THEN
               ChangeSign (Sv[j], Sv[j]);
               SupToBScal (Sv[j], BS);
               BModifVect (W[j], W[i], BS, Dim);
               WWSI[j]^.Negative := TRUE;
               END
            END
         END
      END
   END PairwiseRedDualSI;


PROCEDURE PairwiseRedDual (B : Basis;  i : BDim);
   BEGIN
   WITH  B^  DO
      IF  SISquares  THEN
         PairwiseRedDualSI(B, i)
      ELSE
         PairwiseRedDualLR(B, i)
         END
      END
   END PairwiseRedDual;


PROCEDURE PreRedDieter (B : Basis;  d : BDim);
   VAR
      i : BDim;
      BoundCount : LONGINT;
   BEGIN
   UpdateVVWW (B, d);  SortBasis (B, d);
   WITH  B^  DO
      i := Dim;   cpt := 0;  CountDieter := 0;
      BoundCount := 2 * VAL (LONGINT, Dim) - VAL (LONGINT, d);
      IF  SISquares  THEN
         REPEAT
            PairwiseRedPrimalSI (B, i, d); 
            IF i > d  THEN  PairwiseRedDualSI (B, i)  END;
            IF i <= 1 THEN i := Dim  ELSE  DEC (i)  END
         UNTIL (CountDieter >= BoundCount) OR (cpt > MaxPreRed);
      ELSE
         REPEAT
            PairwiseRedPrimalLR (B, i, d); 
            IF i > d  THEN  PairwiseRedDualLR (B, i)  END;
            IF i <= 1 THEN i := Dim  ELSE  DEC (i)  END
         UNTIL (CountDieter >= BoundCount) OR (cpt > MaxPreRed);
         END;
      END;
   END PreRedDieter;

(**************************************************************************)
(* Procedures for RedLLL.  *)

PROCEDURE CalculGramVD (B : Basis;   VAR GramVD : BASISLR.BMatr);
   (* Retourne dans GramVD la matrice des produits scalaires V[i]*V[j].   *)
   (* Rem.: VVLR ne contient que les V[i]*V[i].   Utilise pour RedLLL.    *)
   VAR
      i, j : BDim;
   BEGIN
   WITH B^ DO
      FOR i := 1 TO Dim DO
         FOR j := i TO Dim DO
            GramVD[i,j] := BProdScalLR (V[i], V[j], Dim);
            GramVD[j,i] := GramVD[i,j]
            END
         END
      END
   END CalculGramVD;


PROCEDURE MiseAJourGramVDLR
   (VAR GramVD : BASISLR.BMatr;
        B      : Basis;
        j      : BDim
   );
   (* Recalcule la jieme ligne et la jieme colonne de la matrice des *)
   (* produits scalaires.  Pour RedLLL.                              *)
   VAR
      i : BDim;
   BEGIN
   WITH B^ DO
      FOR i := 1 TO Dim DO
         GramVD[i,j] := BProdScalLR (V[i], V[j], Dim);
         GramVD[j,i] := GramVD[i,j]
         END
      END
   END MiseAJourGramVDLR;


PROCEDURE PermuteGramVDLR
   (VAR GramVD : BASISLR.BMatr;
        i,j    : BDim;
        n      : BDim
   );
   (* Permute la i-ieme et la j-ieme ligne, et la i-ieme et j-ieme colonne  *)
   (* de la matrice des produits scalaires.   Pour RedLLL.                  *)
   VAR
      k  : BDim;
   BEGIN
   GramVD[0] := GramVD[i];
   GramVD[i] := GramVD[j];
   GramVD[j] := GramVD[0];
   FOR  k := 1  TO  n  DO
      GramVD[k,0] := GramVD[k,i];
      GramVD[k,i] := GramVD[k,j];
      GramVD[k,j] := GramVD[k,0]
      END
   END PermuteGramVDLR;

(**************************************************************************)

PROCEDURE CalculCholeski2LLLLR
   ( VAR Cho2   : BASISLR.BMatr;
     VAR GramVD : BASISLR.BMatr;
         I, j   : BDim);
   (* Recalcule les I premieres entrees de la colonne j de la matrice de *)
   (* Choleski d'ordre 2.   Pour RedLLL.                                 *)
   VAR
      i, k  : BDim;
   BEGIN
   Cho2[1,j] := GramVD[1,j];
   FOR i := 2 TO I DO
      Cho2[i,j] := GramVD[i,j];
      FOR k := 1 TO i-1 DO
         Cho2[i,j] := Cho2[i,j] - (Cho2[k,j]/Cho2[k,k]) * Cho2[k,i]
         END
      END
   END CalculCholeski2LLLLR;


PROCEDURE CalculCholeski2EleLR
   (VAR Cho2   : BASISLR.BMatr;
    VAR GramVD : BASISLR.BMatr;
        i,j    : BDim);
   (* Recalcule l'entree (i,j) de la matrice de Choleski d'ordre 2 *)
   VAR
      k : BDim;
   BEGIN
   Cho2[i,j] := GramVD[i,j];
   FOR k := 1 TO i-1 DO
      Cho2[i,j] := Cho2[i,j] - Cho2[k,i] * (Cho2[k,j]/Cho2[k,k])
      END
   END CalculCholeski2EleLR;

(**************************************************************************)

PROCEDURE ReductionFaible
   (    B      : Basis;
    VAR Cho2   : BASISLR.BMatr;
    VAR GramVD : BASISLR.BMatr;
        i, j   : BDim
   );
   (* Reduit la matrice de Choleski (d'ordre 2) en ajoutant un multiple du *)
   (* vecteur i au vecteur j, si possible.  Modifie le vecteur dual W_i en *)
   (* consequence et remet a jour la matrice des produits scalaires.       *)
   (* Utilise par RedLLL.                                                  *)
   VAR
      cte   : LONGREAL;
      cteLI : LONGINT;
   BEGIN
   WITH B^ DO
      cte := Cho2[i,j] / Cho2[i,i];
      IF ABS (cte) < MaxLongIntLR THEN
         (* On peut representer cte en LONGINT.  *)
         IF ABS(cte) > 0.5 THEN
            cteLI := Round(cte);
            BModifVectLI (V[j], V[i], -cteLI, Dim);
            BModifVectLI (W[i], W[j], cteLI, Dim);
         ELSE
            RETURN
            END;
      ELSE
         (* On represente cte en LONGREAL. *)
         IF ABS(cte) < MaxIntLongReal THEN  cte := TruncLR (cte)  END;
         BModifVectLR (V[j], V[i], -cte, Dim);
         BModifVectLR (W[i], W[j], cte, Dim);
         END;
      IF SISquares THEN
         VVSI [j]^.Negative := TRUE;   WWSI [i]^.Negative := TRUE;
      ELSE
         VVLR [j] := -1.0;      WWLR [i] := -1.0;
         END;
      MiseAJourGramVDLR (GramVD, B, j);
      CalculCholeski2LLLLR (Cho2, GramVD, i, j);
      END;
   END ReductionFaible;

(**************************************************************************)

PROCEDURE RedLLL
   ( B      : Basis;
     fact   : LONGREAL;
     maxcpt : LONGINT;
     Max    : BDim
   );
   (* Effectue la pre-reduction de B au sens de Lenstra-Lenstra-Lovasz.   *)
   (* N'utilise pas les vecteurs VVLR, WWLR, VVSI, WWSI.                  *)
   CONST
      e = 40;
   VAR
      IC     : ARRAY BDim OF BDim;
      h,i,j  : BDim;
      k      : CARDINAL;
      Cho2   : BASISLR.BMatr;
      Cho0ij : LONGREAL;
      limite : LONGREAL;
      GramVD : BASISLR.BMatr;
      cpt    : LONGINT;
   BEGIN
   cpt := 0;   CalculGramVD (B, GramVD);
   WITH B^ DO
      limite := 1.0;
      FOR k := 1 TO e DO limite := limite * 2.0 END;
      limite := IToLR(Dim) * limite;
      Cho2 [1,1] := GramVD[1,1];     Cho2[1,2] := GramVD[1,2];
      IC[1] := 2;
      Cho2 [2,2] := GramVD[2,2] - Cho2[1,2] * (Cho2[1,2] / Cho2[1,1]);
      IC[2] := 2;
      FOR i := 3 TO Dim DO IC[i] := 0 END;
      h := 1;
      WHILE  (h < Max) AND (cpt < maxcpt)  DO
         IF GramVD [h+1, h+1] > limite THEN
            FOR i := h TO 1 BY -1 DO
               ReductionFaible (B, Cho2, GramVD, i, h+1)
               END
         ELSE
            ReductionFaible (B, Cho2, GramVD, h, h+1)
            END;
         CalculCholeski2EleLR (Cho2, GramVD, h+1, h+1);
         IF IC[h+1] = 0 THEN IC[h+1] := h+1 END;
         IF ((Cho2[h+1,h+1]/Cho2[h,h]
               + (Cho2[h,h+1]/Cho2[h,h])*(Cho2[h,h+1]/Cho2[h,h])) < fact) THEN
            INC (cpt);
            Permute(B, h, h+1);
            PermuteGramVDLR (GramVD, h ,h+1, Dim);
            Cho2[h,h] := GramVD[h,h];
            FOR i := 1 TO h-1 DO
               Cho2[i,0]   := Cho2[i,h];
               Cho2[i,h]   := Cho2[i,h+1];
               Cho2[i,h+1] := Cho2[i,0];
               Cho2[h,h]   := Cho2[h,h] - Cho2[i,h]*(Cho2[i,h]/Cho2[i,i])
               END;
            IF h = 1 THEN
               Cho0ij := Cho2[1,2]/Cho2[1,1];
               IF ABS(Cho0ij) > 0.5 THEN
                  IC[1] := 2;   IC[2] := 0;   h := 1
               ELSE
                  Cho2[2,2] := GramVD[2,2] -
                                   Cho2[1,2] * (Cho2[1,2]/Cho2[1,1]);
                  CalculCholeski2LLLLR (Cho2, GramVD, 3, 3);
                  IC[1] := 3;  IC[2] := 3;  IC[3] := 3;   h := 2
                  END
            ELSE
               IC[h] := h + 1; IC[h+1] := 0;   h := h - 1
               END
         ELSE
            FOR i := 1 TO h+2 DO
               IF h+2 > IC[i] THEN
                  IF h+2 <= Dim THEN
                     CalculCholeski2EleLR (Cho2, GramVD, i, h+2) END;
                  IC[i] := h+2
                  END
               END;
            h := h + 1
            END
         END;
      FOR j := 3 TO Max DO
         FOR i := j-2 TO 1 BY -1 DO
            ReductionFaible (B, Cho2, GramVD, i, j);
            END
         END;
      END;
   END RedLLL;

(**************************************************************************)

PROCEDURE SetScale (B : Basis);
   (* Called by ShortestVector and ReductMinkowski when SISquares = TRUE. *)
   (* immediately before doing the BB procedure in REDBB or REDBB0.       *)
   (* Rescales the square lengths of the basis and dual basis vectors     *)
   (* by factors EchVV and EchWW, so that the log of the largest squared  *)
   (* Euclidean length is near 0.                                         *)
   (* Puts the rescaled values in VVLR and WWLR, and the                  *)
   (* rescaled value of m^2 in mLR2.                                      *)
   (* This rescaling is to avoid LONGREAL overflow.                       *)
   VAR
      i : BDim;
      n1, n2, N1, N2 : INTEGER; 
      equal : BOOLEAN;
   BEGIN
   UpdateVVWW (B, 0);
   WITH  B^  DO
      N1 := 0;  N2 := 0;
      FOR  i := 1  TO  Dim  DO
         n1 := NumDigits (VVSI[i]);    IF  n1 > N1  THEN  N1 := n1  END;
         n2 := NumDigits (WWSI[i]);    IF  n2 > N2  THEN  N2 := n2  END
         END;
      IntToSup (1, EchVV);             IntToSup (1, EchWW);
      ShiftLeft (EchVV, N1, EchVV);    ShiftLeft (EchWW, N2, EchWW);
      FOR  i := 1  TO  Dim  DO
         VVLR[i] := DivideLR (VVSI[i], EchVV, equal);
         WWLR[i] := DivideLR (WWSI[i], EchWW, equal)
         END;
      Multiply (EchVV, EchWW, S0);
      mLR2 := DivideLR (mSI2, S0, equal)
      END
   END SetScale;
      
(**************************************************************************)

PROCEDURE NegativeCholeski (B : Basis);
   BEGIN
   WriteLn;
   WriteString ('REDBB0: Negative diagonal element in ');
   WriteString ('Choleski Decomposition !');   
   WriteLn;
   WriteBasis (B);
   END NegativeCholeski;


PROCEDURE CalculCholeski
   (B       : Basis;
    VAR DC2 : BASISLR.BVect;
    VAR C0  : BASISLR.BMatr
   ) : BOOLEAN;
   (* Returns in C0 the elements of the upper triangular matrix of the     *)
   (* Choleski decomposition that are above the diagonal.                  *)
   (* Returns in DC2 the squared elements of the diagonal.                 *)
   (* These elements are rescaled by EchVV when SISquares= TRUE.           *)
   VAR
      i, j, k, d : BDim;
      C2         : BASISLR.BMatr;   (* C2[i,j] = C0[i,j] * C2[i,i] si i#j. *)
                                    (* C2[i,i] = DC2[i].                   *)
      equal      : BOOLEAN;
   BEGIN
   WITH B^ DO
      d := (Dim DIV 2) + 1;
      (* Calcul des d premieres lignes de C0 via la base primale. *)
      FOR  i := 1  TO  d  DO
         FOR  j := i  TO  Dim  DO
            IF  j = i  THEN
               C2[i,i] := VVLR[i]
            ELSE
               IF  SISquares  THEN
                  BProdScalSI (V[i], V[j], Dim, S1);
                  C2[i,j] := DivideLR (S1, EchVV, equal)
               ELSE   
                  C2[i,j] := BProdScalLR (V[i], V[j], Dim)
                  END
               END;
            FOR  k := 1  TO  i-1  DO
               C2[i,j] := C2[i,j] - C0[k,i] * C2[k,j]
               END;
            IF  i = j  THEN
               DC2[i] := C2[i,i];
               IF DC2[i] < 0.0 THEN NegativeCholeski(B);  RETURN FALSE  END;
            ELSE
               C0[i,j] := C2[i,j] / DC2[i]
               END
            END
         END;

      (* Calcul des Dim-d dernieres lignes de C0 via la base duale. *)
      FOR  i := Dim  TO  d+1  BY  -1  DO
         FOR  j := i  TO  1  BY  -1  DO
            IF  j = i  THEN
               C2[i,i] := WWLR[i]
            ELSE
               IF  SISquares  THEN
                  BProdScalSI(W[i], W[j], Dim, S1);
                  C2[i,j] := DivideLR(S1, EchWW, equal)
               ELSE
                  C2[i,j] := BProdScalLR (W[i], W[j], Dim)
                  END
               END;
            FOR  k := i+1  TO  Dim  DO
               C2[i,j] := C2[i,j] - C0[k,i]*C2[k,j]
               END;
            IF  i # j  THEN
               C0[i,j] := C2[i,j]/C2[i,i]
               END
            END;
         DC2[i] := mLR2 / C2[i,i];
         IF DC2[i] < 0.0 THEN NegativeCholeski(B);  RETURN FALSE  END;
         FOR  j := i+1  TO  Dim  DO
            C0[i,j] := -C0[j,i];
            FOR  k := i+1  TO  j-1  DO
               C0[i,j] := C0[i,j] - C0[k,i] * C0[k,j]
               END
            END
         END;
      END;
   RETURN TRUE
   END CalculCholeski;

(**************************************************************************)

PROCEDURE TransformStage3
   ( B     : Basis;
     VAR z : VectLI;
     VAR k : BDim);
   VAR
      i, j : BDim;
      q    : LONGINT;
   BEGIN
   WITH B^ DO
      j := Dim;
      WHILE  z[j] = 0  DO  DEC(j)  END;
      WHILE  ABS(z[j]) > 1  DO
         i := j-1;
         WHILE  z[i] = 0  DO  DEC(i)  END;
         (* On a 2 indices i < j tels que |z_j| > 1 et z_i # 0.           *)
         WHILE  z[j] # 0  DO
            (*  Troncature du quotient vers zero.                         *)
            q := z[i] DIV z[j];
            IF  q # 0  THEN
               (* On ajoute q * v[i] au vecteur V[j].  *)
               z[i] := z[i] - q*z[j];
               BModifVectLI (V[j], V[i], q, Dim);
               BModifVectLI (W[i], W[j], -q, Dim);
               IF  SISquares  THEN
                  VVSI[j]^.Negative := TRUE;   WWSI[i]^.Negative := TRUE;
               ELSE
                  VVLR[j] := -1.0;   WWLR[i] := -1.0
                  END               
               END; 
            (*  Permutation.                                              *)
            z[0] := z[j];   z[j] := z[i];    z[i] := z[0];
            Permute (B, i, j)
            END;  (* WHILE z[j] # 0 *)
         j := i
         END  (* WHILE |z[j]| > 1 *)
      END;
   k := j
   END TransformStage3;

(****************************************************************************)

PROCEDURE TryZ (B : Basis;  j, i : BDim;  Stage : INTEGER) : BOOLEAN;
  (* Si CountNodes > MaxNodes retourne FALSE, sinon retourne TRUE.         *)
  VAR
     min, max       : LONGINT;
     center, dc, x  : LONGREAL;
     zlow, zhigh    : LONGINT;
     high           : BOOLEAN;
     k              : BDim;     
  BEGIN
  INC (CountNodes);
  IF  CountNodes > MaxNodesBB  THEN  RETURN FALSE  END;
  WITH B^ DO
     (* Calcul d'un intervalle contenant les valeurs admissibles de zj. *)
     center := 0.0;
     IF  j < Dim  THEN
	(* Calcul du centre de l'intervalle.                            *)
	FOR  k := j+1  TO  Dim  DO
	   center := center - C0[j,k]*zLR[k]
	   END;

	(* Distance du centre aux extremites de l'intervalle.           *)
	dc := Sqrt((Lmin2 - N2[j])/DC2[j]);

	(* Calcul de deux entiers ayant la propriete qu'un entier       *)
	(* non-compris entre (i.e. strictement exterieur `a) ceux-ci    *)
	(* n'appartient pas a l'intervalle.                             *)
	x := center - dc;   min := Trunc (x);
	IF  x > 0.0  THEN  INC(min)  END;
	x := center + dc;   max := Trunc (x);
	IF  x < 0.0  THEN  DEC(max)  END;

	(* En vue du choix initial de zj. On determine zlow et zhigh.   *)
	IF  min > max  THEN
	   RETURN TRUE
	ELSIF  min = max  THEN
	   zlow := min;  zhigh := max;  INC (zhigh);  high := FALSE
	ELSE
	   IF  center >= 0.0  THEN
	      zlow := Trunc (center);  zhigh := zlow;  INC (zhigh);
	      high := ODD (Trunc (2.0*center));
	   ELSE
	      zhigh := Trunc (center); zlow := zhigh; DEC(zlow);
	      high := NOT ODD (Trunc (2.0*center));
	      END
	   END
     ELSE (* j = Dim *)
	zlow := 0;  high := TRUE;
	IF  Stage = 2  THEN
	   min := 1;  max := 1;  zhigh := 1
	ELSE
	   min := 2;   zhigh := 2;
	   max := Trunc (Sqrt ((Lmin2 - N2[j]) / DC2[j]));
	   END
	END;

     (* On essaie maintenant chacun des z[j] dans l'intervalle, en      *)
     (* commencant par le centre puis en alternant d'un cote a l'autre. *)
     WHILE ((zlow >= min) OR (zhigh <= max)) DO
	IF  high  THEN  
           zLI[j] := zhigh;   INC (zhigh);
	   IF  zlow >= min  THEN  high := FALSE  END
	ELSE
	   zLI[j] := zlow;    DEC (zlow);
	   IF  zhigh <= max  THEN  high := TRUE  END
	   END;
	zLR[j] := LIToLR(zLI[j]);

	(* Calcul de N2[j-1].                                           *)
	x := zLR[j] - center;
	N2[j-1] := N2[j] + x*x*DC2[j];

	IF  j = 1  THEN
	   IF  N2[0] < Lmin2 THEN
	      (* On verifie si on a vraiment trouve un vecteur plus court. *)
	      BCopyVect(V[Dim], V[0], Dim);
	      FOR  k := 1  TO  Dim - 1  DO
		 IF zLI[k] # 0 THEN BModifVectLI(V[0], V[k], zLI[k], Dim) END
		 END;
	      IF Stage = 3 THEN
		 BModifVectLR(V[0], V[Dim], zLR[Dim] - 1.0, Dim)
		 END;
	      IF  SISquares  THEN
		 BProdScalSI (V[0], V[0], Dim, S1);
		 IF  Smaller (S1, VVSI[Dim])  THEN
		    IF  Stage = 2  THEN
		       smaller := TRUE;
		       IF  (NOT PreRedLLLRM)  THEN
			  zshort := zLI
		       ELSE
			  FOR  k := 1  TO  Dim-1  DO
			     BProdScalSI (V[0], WTemp[k], Dim, S2);
			     Divide (S2, mSI, S3, S4);
			     SupToInt (S3, zshort[k])
			     END;
			  zshort[Dim] := 1
			  END
		    ELSIF  (Stage = 3) AND (NOT PreRedLLLRM) THEN
		       IF  GCD2vect(zLI, i, Dim) = 1  THEN
			  zshort := zLI;  smaller := TRUE
			  END
		    ELSE
		       FOR  k := 1  TO  Dim  DO
			  BProdScalSI (V[0], WTemp[k], Dim, S2);
			  Divide (S2, mSI, S3, S4);
			  SupToInt (S3, zshort[k])
			  END;
		       IF  GCD2vect (zshort, i, Dim) = 1  THEN
			  smaller := TRUE
			  END
		       END;
		    IF  smaller  THEN
		       Affect (S1, VVSI[Dim]);
                       (*  Lmin2 := DivideLR (S1, EchVV, equal);  *)
		       RETURN  TRUE
		       END
		    END
	      ELSE  (* NOT SISquares  *)
		 x := BProdScalLR (V[0], V[0], Dim);
		 IF  x < Lmin2  THEN
		    IF  Stage = 2  THEN
		       smaller := TRUE;
		       IF  (NOT PreRedLLLRM)  THEN
			  zshort := zLI
		       ELSE
			  FOR  k := 1  TO  Dim-1  DO
			     zshort[k] := 
                                Round (BProdScalLR(V[0], WTemp[k], Dim)/mLR)
			     END;
			  zshort[Dim] := 1
			  END
		    ELSIF (Stage = 3) AND (NOT PreRedLLLRM) THEN
		       IF  GCD2vect (zLI, i, Dim) = 1  THEN
			  zshort := zLI;   smaller := TRUE
			  END
		    ELSE
		       FOR  k := 1  TO  Dim  DO
			  zshort[k]:=
			     Round (BProdScalLR (V[0], WTemp[k], Dim)/mLR)
			  END;
		       IF GCD2vect (zshort, i, Dim) = 1 THEN smaller := TRUE END
		       END;
		    IF  smaller  THEN  
                       (*  Lmin2 := x;  *)
		       VVLR[Dim] := x;   RETURN TRUE
		       END
		    END
		 END
	      END
	ELSE  (* j # 1 *)
	   IF  Lmin2 >= N2[j-1]  THEN
	      IF  NOT TryZ (B, j-1, i, Stage) THEN RETURN FALSE  END;
              (* Des qu'on a trouve quelque chose, on sort de la recursion  *)
              (* et on retourne dans ReductMinkowski.                       *)
	      IF  smaller  THEN  RETURN TRUE  END
	      END
	   END;
	END;
     RETURN TRUE
     END
  END TryZ;

PROCEDURE REDBB (B : Basis;  i, d : BDim;  Stage : INTEGER) : BOOLEAN;
   (* Tries to shorten V[i] using branch-and-bound. Stage is 2 or 3.        *)
   (* z[i] = 1 if Stage = 2, z[i] >= 2 if Stage = 3.                        *)
   (* Stops and returns FALSE if not finished after examining MaxNodes      *)
   (* nodes in the branch-and-bound tree.  When succeeds, returns TRUE.     *)
   (* Assumes that the norm is Euclidean.                                   *)
   VAR
      h, k : BDim;
   BEGIN
   UpdateVVWW (B, 0);  SortBasis (B, 0);
   smaller := FALSE;
   WITH B^ DO
      (*  Approximation du carre de la longueur de Vi. Celle-ci est       *)
      (*  normalisee dans le cas SISquares.                               *)
      Lmin2 := VVLR[i];
      IF  (Stage = 3)  THEN
         IF  (Lmin2 * WWLR[i] < 4.0 * mLR2)  THEN  RETURN TRUE  END
         END;
      Permute (B, i, Dim);

      IF PreRedLLLRM THEN
         (* On memorise la base courante.   *)
         BCopyMatr (V, VTemp, Dim);   BCopyMatr (W, WTemp, Dim);
         FOR h := 1 TO Dim DO
            VVLRTemp[h] := VVLR[h];   WWLRTemp[h] := WWLR[h]
            END;
         RedLLL (B, 1.0, 1000000, Dim-1);
         UpdateVVWW (B, 0);
         END;

      IF NOT CalculCholeski (B, DC2, C0) THEN RETURN FALSE END;
      CountNodes := 0;
      N2[Dim] := 0.0;
      IF  NOT TryZ (B, Dim, i, Stage) THEN  RETURN FALSE  END;

      IF PreRedLLLRM THEN
         (* On remet l'anciennne base, celle d'avant LLL, avant de considerer
            la prochaine dimension.                                        *)
         BCopyMatr (VTemp, V, Dim);  BCopyMatr (WTemp, W, Dim);
         FOR  h := 1  TO  Dim  DO
            VVLR[h] := VVLRTemp[h];  WWLR[h] := WWLRTemp[h]
            END
         END;

      IF smaller THEN
         (* On a trouve un plus court vecteur.  On ameliore V[k].  *)
         IF  Stage = 2  THEN
            k := Dim;
         ELSE
            TransformStage3 (B, zshort, k);
            END;
         BCopyVect (V[0], V[k], Dim);
         IF  SISquares  THEN
            VVSI[k]^.Negative := TRUE
         ELSE
            VVLR[k] := -1.0
            END;
         IF  zshort[k] < 0  THEN  BChangeSignVect (W[k], Dim)  END;
         (* Mise a jour des vecteurs de la base duale selon le nouveau V[k]. *)
         FOR  h := 1  TO  Dim  DO
            IF  (zshort[h] # 0) AND (h # k) THEN
               BModifVectLI(W[h], W[k], -zshort[h], Dim);
               IF  Stage = 2  THEN
                  IF  h > d  THEN  XX[h] := FALSE  END
                  END;
               IF  SISquares  THEN
                  WWSI[h]^.Negative := TRUE
               ELSE
                  WWLR[h] := -1.0
                  END
               END
            END
      ELSE
         IF  Stage = 2  THEN  XX[Dim] := TRUE  END
         END;
      Permute (B, i, Dim);
      RETURN TRUE
      END
   END REDBB;

(************************************************************************)

PROCEDURE ReductMinkowski (B : Basis;  d : BDim) : BOOLEAN;
   VAR
      i          : BDim;
      TotalNodes : LONGINT;
   BEGIN
   TotalNodes := 0;
   WITH B^ DO
      REPEAT
         (* The first d vectors should not be modified.                   *)
         FOR  i := 1 TO d  DO  XX[i] := TRUE  END;
         FOR  i := d + 1  TO  Dim  DO  XX[i] := FALSE  END;
         REPEAT
            PreRedDieter (B, d);
            IF  SISquares  THEN  SetScale (B) END;
            FOR i := 1 TO Dim  DO
               IF  NOT XX[i]  THEN
                  (* On essaie de reduire le i-ieme vecteur.              *)
                  IF  NOT REDBB (B, i, d, 2) THEN  RETURN FALSE END;
                  INC (TotalNodes, CountNodes);
                  END
               END
         UNTIL NOT smaller;

         (* Stage 3.                                                      *)
         IF Dim > 7 THEN
            FOR i := d + 1 TO Dim DO
               IF NOT REDBB (B, i, d, 3) THEN  RETURN FALSE  END;
               INC (TotalNodes, CountNodes);
               END
            END
      UNTIL NOT smaller;
      IF (TotalNodes > MinkLLL) AND (NOT SISquares) THEN 
         PreRedLLLRM := TRUE 
         END;
      (*
      VVLR [1]   := BProdScalLR (V[1], V[1], Dim);
      VVLR [Dim] := BProdScalLR (V[Dim], V[Dim], Dim);
      *)
      END;
   RETURN TRUE
   END ReductMinkowski;

(************************************************************************)

PROCEDURE TryZ0 (B : Basis;  j : BDim) : BOOLEAN;
   (* Procedure recursive implantant le BB pour ShortestVector (REDBB0).  *)
   (* Si CountNodes > MaxNodes, retourne FALSE.                           *)
   (* Sinon, retourne TRUE: on a trouve le plus court vecteur.            *) 

   (* Le carre de la longueur du plus court vecteur a date est dans Lmin2.*)
   (* Si j=1 et on trouve un plus court vecteur, on retrouve les zj       *)
   (* correspondants dans zshort.                                         *)

  VAR
     (* Note: Pour une implantation non recursive, ces variables devraient*)
     (* etre des tableaux indices par j.                                  *)
     center, x, dc : LONGREAL;
     min, max      : LONGINT;  (* Bornes de l'intervalle pour les z_j.    *)
     zlow, zhigh   : LONGINT;  (* Valeur courante examinee a gauche et a  *)
                               (* droite du centre.                       *)
     high          : BOOLEAN;  (* Indique si on est a d. ou g. du centre. *)
     equal         : BOOLEAN;
     k             : BDim;
  BEGIN
  INC (CountNodes);
  IF  CountNodes > MaxNodesBB  THEN  RETURN FALSE  END;
  WITH  B^  DO
     (* Calcul d'un intervalle contenant les valeurs admissibles de zj.   *)

     (* Calcul du centre de l'intervalle.                                 *)
     center := 0.0;
     FOR k := j+1 TO Dim  DO center := center - C0[j,k] * zLR[k] END;

     (* Distance du centre aux extremites de l'intervalle.                *)
     dc := Sqrt ((Lmin2 - N2[j])/DC2[j]);

     (* Calcul de deux entiers ayant la propriete qu'un entier            *)
     (* non-compris entre (i.e. strictement exterieur `a) ceux-ci         *)
     (* n'appartient pas a l'intervalle.                                  *)
     (* Si NOT FoundZero on pose min egal a zero par symetrie.            *)
     IF  NOT FoundZero  THEN
	min := 0
     ELSE
	x := center - dc;   min := Trunc (x);
	IF  x > 0.0  THEN  INC (min)  END
	END;
     x := center + dc;     max := Trunc (x);
     IF  x < 0.0  THEN  DEC(max)  END;

     (* En vue du choix initial de zj. On determine zlow et zhigh.      *)
     IF  min > max  THEN
	RETURN TRUE
     ELSIF  min = max  THEN
	zlow := min;  zhigh := max + 1;   high := FALSE
     ELSE
	IF  center >= 0.0  THEN
	   zlow  := Trunc (center);  zhigh := zlow + 1;
	   high  := ODD (Trunc (2.0 * center))
	ELSE
	   zhigh := Trunc (center);  zlow  := zhigh - 1;
	   high  := NOT ODD (Trunc (2.0 * center))
	   END
	END;

     (* On essaie maintenant chacun des z[j] dans l'intervalle, en      *)
     (* commencant par le centre puis en alternant d'un cote a l'autre. *)
     WHILE ((zlow >= min) OR (zhigh <= max)) DO
	IF  high  THEN  
           zLI[j] := zhigh;   INC (zhigh);
	   IF  zlow >= min  THEN  high := FALSE  END
	ELSE
	   zLI[j] := zlow;    DEC (zlow);
	   IF  zhigh <= max  THEN  high := TRUE  END
	   END;
	zLR[j] := LIToLR(zLI[j]);

	(* Calcul de N2[j-1], qui est normalise dans le cas SISquares.  *)
	x := zLR[j] - center;
	N2[j-1] := N2[j] + x * x * DC2[j];

	IF  j = 1  THEN
           (* Tous les zj sont choisis: on a un vecteur a tester.       *)
	   IF  Lmin2 > N2[0]  THEN
	      (* On verifie si on a vraiment trouve un vecteur          *)
	      (* non-nul et plus court.                                 *)
	      IF  NOT FoundZero  THEN
                 (* Le premier vecteur trouve sera zero.                *)
		 FoundZero := TRUE
	      ELSE
		 BCopyVect (ZeroVect, V[0], Dim);
		 FOR  k := 1  TO  Dim  DO
		    IF  zLI[k] # 0  THEN
		       BModifVectLI (V[0], V[k], zLI[k], Dim)
		       END
		    END;
                 (* Le nouveau vecteur trouve est maintenant dans V[0].    *)
		 IF  SISquares  THEN
                    IF Norm = L2Norm THEN
                       BProdScalSI (V[0], V[0], Dim, S1);
                    ELSIF Norm = L1Norm THEN
                       BL1NormSI (V[0], Dim, S1);   Multiply (S1, S1, S1);
                       END;
		    x := DivideLR (S1, EchVV, equal);
		 ELSE
                    IF Norm = L2Norm THEN
	               x := BProdScalLR (V[0], V[0], Dim);
                    ELSIF Norm = L1Norm THEN
                       x := BL1NormLR (V[0], Dim);  x := x * x;
                       END;
                    END;
                 IF  x < Lmin2  THEN
                    (* Il est plus court!  *)
		    smaller := TRUE;   Lmin2 := x;   zshort := zLI;
                    BCopyVect (V[0], W[0], Dim);
		    END
		 END
	      END
	ELSE
	   IF  Lmin2 > N2[j-1]  THEN
              (* Encore de l'espoir: recursion.   *)
	      IF  NOT TryZ0 (B, j-1) THEN  RETURN FALSE  END
	      END
	   END
	END
     END;
  RETURN TRUE
  END TryZ0;


PROCEDURE REDBB0 (B : Basis) : BOOLEAN;
   (* Finds shortest non-zero vector, using branch-and-bound.              *)
   (* Stops and returns FALSE if not finished after examining MaxNodes     *)
   (* nodes in the branch-and-bound tree.  When succeeds, returns TRUE,    *)
   (* and the shortest vector square length will be in Lmin2.              *)
   VAR
      h, k : BDim;
      x : LONGREAL;
      equal : BOOLEAN;
   BEGIN
   WITH B^ DO
      UpdateVVWW (B, 0);   SortBasis (B, 0);
      (* Approximation du carre de la longueur du plus court vecteur.     *)
      (* Celle-ci est normalisee dans le cas SISquares.                   *)
      IF  SISquares  THEN
         IF Norm = L2Norm THEN
            Lmin2 := DivideLR (VVSI[1], EchVV, equal)
         ELSE  (*  Norm = L1Norm  *)
            BL1NormSI (V[1], Dim, S1);
            FOR k := 2 TO Dim DO  
                BL1NormSI (V[k], Dim, S2);
                IF Smaller (S2, S1) THEN Affect (S2, S1) END;
                END;
            Multiply (S1, S1, S1);
            Lmin2 := DivideLR (S1, EchVV, equal)
            END;
      ELSE
         IF Norm = L2Norm THEN
            Lmin2 := VVLR [1]
         ELSE  (*  Norm = L1Norm  *)
            Lmin2 := BL1NormLR (V[1], Dim);
            FOR k := 2 TO Dim DO
                x := BL1NormLR (V[k], Dim);
                IF x < Lmin2 THEN Lmin2 := x END;
                END;
            Lmin2 := Lmin2 * Lmin2;
            END;
         END;

      IF NOT CalculCholeski (B, DC2, C0) THEN RETURN FALSE END;
      (* On effectue le branch and bound.                                  *)
      (* N2[j] sera la somme des termes |z*k|^2 ||v*k||^2 pour k > j.      *)
      N2[Dim] := 0.0;
      CountNodes := 0;   smaller := FALSE;   FoundZero := FALSE;
      IF NOT TryZ0 (B, Dim) THEN  RETURN FALSE  END;

      IF  smaller  THEN
         (* We have found a shorter vector.         *)
         (* Its square length is in Lmin2.          *)
         TransformStage3 (B, zshort, k);
         BCopyVect (W[0], V[k], Dim);
         IF  SISquares  THEN
            VVSI[k]^.Negative := TRUE
         ELSE
            VVLR[k] := -1.0
            END;
         (* The new shorter vector is now in V[k].     *)
         (* We update the vectors of the dual basis.   *)
         IF  zshort[k] < 0  THEN  BChangeSignVect (W[k], Dim) END;
         FOR  h := 1 TO Dim  DO
            IF (zshort[h] # 0) AND (h # k) THEN
               BModifVectLI (W[h], W[k], -zshort[h], Dim);
               IF  SISquares  THEN
                  WWSI[h]^.Negative := TRUE
               ELSE
                  WWLR[h] := -1.0
                  END
               END
            END
         END
      END;
   RETURN TRUE
   END REDBB0;

(**************************************************************************)

PROCEDURE REDDiet (B : Basis) : BOOLEAN;
   (* Finds shortest non-zero vector with specified norm.                  *)
   (* Does not modify the basis.                                           *)
   (* Stops and returns FALSE if not finished after examining possib.      *)
   (* When succeeds, returns TRUE, and returns length in Lmin.             *)
   (* Uses the algorithm of Dieter (1975), given in Knuth (1981).          *)
   VAR
      k            : BDim;
      z, Supz      : ARRAY BDim OF LONGINT;
      x            : LONGREAL;
      ProcNorm     : PROCEDURE (VAR BVect, BDim) : LONGREAL;
   BEGIN
   WITH B^ DO
      CASE Norm OF
         L2Norm  : ProcNorm := BL2NormLR;
       | L1Norm  : ProcNorm := BL1NormLR;
       | SupNorm : ProcNorm := BSupNormLR;
         END;

      (* Compute the bounds in eq.(7) of Dieter (1975).                *)      
      (* For this, VVLR and WWLR temporarily hold the vector norms.    *)
      FOR k := 1 TO Dim DO  
          VVLR [k] := ProcNorm (V[k], Dim);
          WWLR [k] := ProcNorm (W[k], Dim);
          END;
      SortBasis (B, 0);
      (* Basis is now sorted according to the desired norm.            *)
      Lmin := VVLR [1];
      FOR k := 1 TO Dim DO
          Supz [k] := Trunc (0.000000001 + WWLR [k] * Lmin / mLR);
          z[k] := 0;
          END;

      (* Algorithm given in Knuth (1981).  Memoire de F. Blouin, p. 25. *)
      CountNodes := 0;   smaller := FALSE; 
      BCopyVect (ZeroVect, Y, Dim);  (*  Met Y a zero. *)
      k := Dim;
      WHILE k >= 1 DO
         IF z[k] < Supz[k] THEN
            INC (z[k]);  BModifVectLI (Y, V[k], 1, Dim);
            WHILE k < Dim DO
               INC (k);   z[k] := -Supz[k];   
               BModifVectLI (Y, V[k], 2 * z[k], Dim);
               END;
            x := ProcNorm (Y, Dim);
            IF x < Lmin THEN  Lmin := x;  smaller := TRUE  END;
         ELSE
            DEC (k)
            END
         END;
      FOR k := 1 TO Dim DO  VVLR [k] := -1.0;  WWLR [k] := -1.0  END;
      END;
   RETURN TRUE
   END REDDiet;

(**************************************************************************)

PROCEDURE ShortestVector (B : Basis) : BOOLEAN;
   (* Square length of shortest vector can be recovered in B^.Lmin2.  *)
   VAR
      OK : BOOLEAN;
   BEGIN
   WITH B^ DO
      (* Perform pre-reductions using L_2 norm. *)
      IF PreRedDieterSV THEN  PreRedDieter (B, 0)  END;
      IF PreRedLLLSV    THEN  RedLLL (B, 0.999999, 1000000, Dim) END;
      (* Find the shortest vector for the selected norm.                    *)
      (* The L_2 norm is used for the Choleski decomposition and BB bounds. *)
      IF SISquares THEN  SetScale (B) END;
      IF (Norm = L1Norm) OR (Norm = L2Norm) THEN
         OK := REDBB0 (B)
      ELSE
         OK := FALSE;
         Error ("REDBAS.ShortestVector : wrong norm")
         END;
      IF (CountNodes > ShortDiet) THEN  PreRedDieterSV := TRUE  END;
      IF (CountNodes > ShortLLL) AND (NOT SISquares) THEN
         PreRedLLLSV := TRUE
         END;
      RETURN OK;
      END;
   END ShortestVector;

(*************************************************************************)

PROCEDURE ShortestVectorDiet (B : Basis) : BOOLEAN;
   (* Length of shortest vector can be recovered in B^.Lmin.  *)
   VAR
      OK : BOOLEAN;
   BEGIN
   WITH B^ DO
      (* Perform pre-reductions using L_2 norm. *)
      IF PreRedDieterSV THEN  PreRedDieter (B, 0) END;
      IF PreRedLLLSV    THEN  RedLLL (B, 0.999999, 1000000, Dim) END;
      (* Find the shortest vector for the selected norm.                    *)
      OK := REDDiet (B);
      IF (CountNodes > ShortDiet) THEN  PreRedDieterSV := TRUE  END;
      IF (CountNodes > ShortLLL) AND (NOT SISquares) THEN
         PreRedLLLSV := TRUE
         END;
      RETURN OK;
      END;
   END ShortestVectorDiet;

(*************************************************************************)

BEGIN
CurMaxDim      := 0;
PreRedDieterSV := TRUE;
PreRedLLLSV    := FALSE;
PreRedLLLRM    := FALSE;
ShortLLL       := 1000;
ShortDiet      := 1000;
MinkLLL        := 500000;
MaxPreRed      := 1000000;
MaxNodesBB     := 10000000;  
Create(S0, 2);  Create(S1, 2);  Create(S2, 2); 
Create(S3, 2);  Create(S4, 2);
BCreateScal (BS);
END REDBAS.
