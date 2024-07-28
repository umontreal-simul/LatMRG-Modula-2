IMPLEMENTATION MODULE LATBASIS;


FROM Storage  IMPORT ALLOCATE, DEALLOCATE;
FROM SYSTEM   IMPORT ADDRESS;
FROM MYINOUT  IMPORT WriteString, WriteLn, WriteCard, ReadCard, ReadLn,
                     Assert, Error, WriteInt;

FROM SUPINT   IMPORT SuperInteger, Create, Delete, NumDigits, WriteSup,
                     ReadSup, NumBits;
FROM SUPCONV  IMPORT IntToSup;
FROM SUPARITH IMPORT Smaller, Negative, Multiply, Equal, Subtract, Add, Zero,
                     Divide, CutLeft, ShiftLeft, ChangeSign, AbsSizeOrd;

FROM CONFIG   IMPORT BDim;
FROM NORM     IMPORT NormType;
FROM MULT     IMPORT MScal, MCreateScal, MScalToLR, MScalToSup;
FROM CONVERT  IMPORT BScalToSup, SupToBScal;
FROM BASIS    IMPORT BZero, BScal, BVect, BMatr, BDeleteVect, BCreateVect,
                     BDeleteMatr, BCreateMatr, BCopyMatr, BExchange,
                     BDivideRound, BProdScalSI, BProdScalLR, BL1NormLR,
                     BSupNormLR, BL1NormSI, BSupNormSI, BReadScal, BWriteScal,
                     BAffectIdentMatr;
IMPORT BASISLR;
IMPORT BASISSI;


VAR
   S1, S2  : SuperInteger;
   tempMS  : MScal;


PROCEDURE CreateBasis (VAR B : Basis);
   BEGIN
   NEW (B);
   WITH B^ DO 
      Create (mSI, 2);    Create (mSI2, 2);
      Create (EchVV, 2);  Create (EchWW, 2);
      ResDim := 0;  Dim := 0;  Norm := L2Norm;  mLR := 0.0;
      SISquares := FALSE;
      END
   END CreateBasis;


PROCEDURE InitBasis (B : Basis;  m : MScal;  Nor : NormType;  d : BDim);
   (* Allocates memory for the basis elements up to d dimensions if d > 0. *)
   (* For d=0, recovers all the memory.                                    *) 
   (* If d = ResDim, does nothing.                                         *)
   VAR
      i, d1 : BDim;
   BEGIN
   WITH B^ DO
      Norm := Nor;   mLR  := MScalToLR(m);   mLR2 := mLR * mLR;  
      MScalToSup (m, mSI);
      IF (NumDigits (mSI) > 33) THEN 
         SISquares := TRUE;
         Multiply (mSI, mSI, mSI2);
      ELSE
         SISquares := FALSE
         END;
      IF d < ResDim THEN
         IF d = 0 THEN d1 := 0 ELSE d1 := d+1 END;
         BDeleteMatr (V, d1, ResDim);  BDeleteMatr (W, d1, ResDim);
         BASISSI.BDeleteVect (VVSI, d1, ResDim);
         BASISSI.BDeleteVect (WWSI, d1, ResDim);
      ELSIF d > ResDim THEN
         IF ResDim = 0 THEN d1 := 0 ELSE d1 := ResDim+1 END;
         BCreateMatr (V, d1, d);  BCreateMatr (W, d1, d);
         BASISSI.BCreateVect (VVSI, d1, d);  
         BASISSI.BCreateVect (WWSI, d1, d);
         END;
      ResDim := d;
      FOR i := 1 TO d DO 
         VVLR[i] := -1.0;  WWLR[i] := -1.0;
         BASISSI.BAffect (BASISSI.BMinusOne, VVSI[i]);  
         BASISSI.BAffect (BASISSI.BMinusOne, WWSI[i]);
         END
      END
   END InitBasis;
 
(****************************************************************************)

PROCEDURE DeleteBasis (B : Basis);
   BEGIN
   InitBasis (B, tempMS, B^.Norm, 0);
   Delete (B^.mSI);     Delete (B^.mSI2);
   Delete (B^.EchVV);   Delete (B^.EchWW);
   DISPOSE (B)
   END DeleteBasis;

(****************************************************************************)

PROCEDURE WriteBasis (B : Basis);
   VAR
      i, j : BDim;
   BEGIN
   WriteString('---------------------------------------------------- Basis');
   WriteLn;
   WITH B^ DO
      WriteCard (Dim, 10);   WriteString('                 <-- Dim');
      WriteLn;
      BASISSI.BWriteScal (mSI, 40);  WriteString('         <--  m ');
      WriteLn;  WriteLn;      
      FOR i := 1 TO Dim DO
         FOR j := 1 TO Dim DO
            BScalToSup (V[i,j], S1);
            WriteSup (S1, 10, 30);   WriteString ('   ');
            BScalToSup (W[i,j], S1);   WriteSup (S1, 10, 30);   
            WriteString('         <-- V['); WriteInt(i,1);
            WriteString(','); WriteInt(j,1);
            WriteString('],     W['); WriteInt(i,1);
            WriteString(','); WriteInt(j,1);
            WriteString(']');
            WriteLn
            END;
         WriteLn
         END
      END
   END WriteBasis;

PROCEDURE ReadBasis (VAR B : Basis);
   VAR
      i, j : BDim;
      temp : CARDINAL;
   BEGIN
   ReadLn;
   WITH B^ DO
      ReadCard (temp);  ReadLn;
      Dim := VAL (BDim, temp);   BASISSI.BReadScal (mSI);  ReadLn; ReadLn;
      FOR i := 1 TO Dim DO
         FOR j := 1 TO Dim DO
            BReadScal (V[i,j]);  BReadScal (W[i,j]);  ReadLn
            END;
         ReadLn
         END
      END
   END ReadBasis;

(**************************************************************************)

PROCEDURE CopyBasis (B1, B2 : Basis);
   (* Assumes that B2^.ResDim >= B1^.Dim   *) 
   VAR
      i :BDim;
   BEGIN
   IF (B2^.ResDim < B1^.Dim) THEN
      Error ("CopyBasis: B2^.ResDim < B1^.Dim");
      END;
   WITH B1^ DO
      B2^.Dim  := Dim;
      B2^.mLR  := mLR;
      B2^.mLR2 := mLR2;
      B2^.Norm := Norm;
      B2^.Lmin  := Lmin;
      B2^.Lmin2 := Lmin2;
      B2^.SISquares := SISquares;
      BASISSI.BAffect (mSI,  B2^.mSI);
      BASISSI.BAffect (mSI2, B2^.mSI2);
      BCopyMatr (V, B2^.V, Dim);   
      BCopyMatr (W, B2^.W, Dim);
      BASISLR.BCopyVect (VVLR, B2^.VVLR, Dim); 
      BASISLR.BCopyVect (WWLR, B2^.WWLR, Dim);
      BASISSI.BCopyVect (VVSI, B2^.VVSI, Dim); 
      BASISSI.BCopyVect (WWSI, B2^.WWSI, Dim);
      BASISSI.BAffect (EchVV, B2^.EchVV);
      BASISSI.BAffect (EchWW, B2^.EchWW);
      FOR i := 1 TO Dim DO
         B2^.XX[i] := XX[i];
         END
      END
   END CopyBasis;

(**************************************************************************)

PROCEDURE Permute (B : Basis;  i, j : BDim);
   (* Exchanges vectors i and j in the basis and its dual.                 *) 
   VAR 
      k : BDim;  t : LONGREAL;  adr : ADDRESS;  p : BOOLEAN;
   BEGIN
   WITH B^ DO
      FOR k := 1 TO Dim DO
         BExchange(V[j,k], V[i,k]);  BExchange(W[j,k], W[i,k])
         END;
      t   := VVLR[j];    VVLR[j] := VVLR[i];    VVLR[i] := t;
      t   := WWLR[j];    WWLR[j] := WWLR[i];    WWLR[i] := t;
      adr := VVSI[j];    VVSI[j] := VVSI[i];    VVSI[i] := adr;
      adr := WWSI[j];    WWSI[j] := WWSI[i];    WWSI[i] := adr;
      p   := XX[j];        XX[j] := XX[i];        XX[i] := p
      END
   END Permute;


PROCEDURE SortBasis (B : Basis;  d : BDim);
   VAR
      i, j, k : BDim;
   BEGIN
   (* We assume that the square lengths are already updated.               *)
   (* This gives flexibility to the user to put something else than        *)
   (* the square Euclidean length in VVLR, WWLR, etc.                      *)
   WITH B^ DO
      IF  SISquares  THEN
         FOR  i := d + 1  TO  Dim-1  DO
            k := i;  
            FOR  j := i+1  TO  Dim  DO
               IF  Smaller (VVSI[j], VVSI[k])  THEN  k := j  END
               END;
            IF  i # k  THEN  Permute (B, i, k) END
            END;
         Assert ((NOT VVSI[d+1]^.Negative), "Negative VVSI in SortBasis");
      ELSE
         FOR  i := d + 1  TO  Dim-1  DO
            k := i;
            FOR  j := i+1  TO  Dim  DO
               IF  VVLR[j] < VVLR[k]  THEN  k := j  END
               END;
            IF  i # k  THEN  Permute (B, i, k) END
            END;
(*
         (* This should be faster if the basis is already sorted.         *)
         FOR  i := d + 2  TO  Dim  DO
            (* On trouve la place de V[i] dans V[d+1..i-1].  *)
            x := VVLR [i];   j := i-1;
            WHILE (j > d) AND (x < VVLR[j]) DO  
               Permute (B, j, j+1);  DEC (j)
               END;
            END;
*)
         Assert (NOT (VVLR[d+1] < 0.0), "Negative VVLR in SortBasis");
         END
      END
   END SortBasis;

(**************************************************************************)

PROCEDURE Dualize (B : Basis);
   VAR
      i, j : BDim;  s : BScal;  adr : ADDRESS;  t : LONGREAL;
   BEGIN
   WITH B^ DO
      FOR i := 1 TO Dim DO
         FOR j := 1 TO Dim DO
            s := V[i,j];  V[i,j] := W[i,j];  W[i,j] := s
            END;
         t   := VVLR[i];  VVLR[i] := WWLR[i];  WWLR[i] := t;
         adr := VVSI[i];  VVSI[i] := WWSI[i];  WWSI[i] := adr;
         END;
      adr := EchVV;   EchVV := EchWW;   EchWW:= adr;
      END
   END Dualize;

(**************************************************************************)

(*
PROCEDURE UpdateVV (B : Basis;  d : BDim);
   (* Updates VVLR or VVSI from d+1 to Dim.  *)
   VAR
      i : BDim;
   BEGIN
   WITH B^ DO
      IF  SISquares  THEN
         FOR  i := d+1  TO  Dim  DO
            IF VVSI[i]^.Negative  THEN
               BProdScalSI (V[i], V[i], Dim, VVSI[i])
               END
            END
      ELSE
         FOR  i := d+1  TO  Dim  DO
            IF  VVLR[i] < 0.0  THEN
               VVLR[i] := BProdScalLR (V[i], V[i], Dim)
               END
            END
         END
      END
   END UpdateVV;

(**************************************************************************)

PROCEDURE UpdateWW (B : Basis;  d : BDim);
   (* Updates WWLR or WWSI from d+1 to Dim.  *)
   VAR
      i : BDim;
   BEGIN
   WITH B^ DO
      IF  SISquares  THEN
         FOR  i := d+1  TO  Dim  DO
            IF WWSI[i]^.Negative  THEN
               BProdScalSI (W[i], W[i], Dim, WWSI[i])
               END
            END
      ELSE
         FOR  i := d+1  TO  Dim  DO
            IF  WWLR[i] < 0.0  THEN
               WWLR[i] := BProdScalLR (W[i], W[i], Dim)
               END
            END
         END
      END
   END UpdateWW;
*)

(**************************************************************************)

PROCEDURE UpdateVVWW (B : Basis;  d : BDim);
   VAR
      i : BDim;
   BEGIN
   WITH B^ DO
      IF  SISquares  THEN
         FOR  i := d+1  TO  Dim  DO
            IF VVSI[i]^.Negative  THEN
               BProdScalSI (V[i], V[i], Dim, VVSI[i])
               END;
            IF WWSI[i]^.Negative THEN
               BProdScalSI (W[i], W[i], Dim, WWSI[i])
               END
            END
      ELSE
         FOR  i := d+1  TO  Dim  DO
            IF  VVLR[i] < 0.0  THEN
               VVLR[i] := BProdScalLR (V[i], V[i], Dim)
               END;
            IF  WWLR[i] < 0.0  THEN
               WWLR[i] := BProdScalLR (W[i], W[i], Dim)
               END
            END
         END
      END
   END UpdateVVWW;

(**************************************************************************)

PROCEDURE RandomLattice (B : Basis;   m : BScal;   d : BDim);
   BEGIN
   Error ("RandomLattice ne fonctionne pas encore");
   END RandomLattice;

PROCEDURE EraseVVWW (B : Basis);
   VAR
      i : BDim;
   BEGIN
   WITH B^ DO
      IF  SISquares  THEN
         FOR i := 1 TO Dim DO 
            BASISSI.BAffect (BASISSI.BMinusOne, VVSI[i]);  
            BASISSI.BAffect (BASISSI.BMinusOne, WWSI[i]);
            END
      ELSE
         FOR i := 1 TO Dim  DO
            VVLR[i] := -1.0;  WWLR[i] := -1.0;
            END
         END
      END;
   END EraseVVWW;

(**************************************************************************)

PROCEDURE CheckDuality (B : Basis): BOOLEAN;
   VAR
      i, j : BDim;
   BEGIN
   WITH  B^  DO      
      FOR i := 1 TO Dim DO
         FOR j := 1 TO Dim DO
            BProdScalSI(V[i], W[j], Dim, S1);
            IF  j<>i  THEN  
               IF NOT Equal(S1, BZero) THEN
                  WriteString ("Duality FALSE:   V[");
                  WriteInt(i, 1);  WriteString ("].W["); WriteInt(j, 1);
                  WriteString ("]"); WriteLn;
                  RETURN FALSE;
                  END
            ELSE
               IF NOT Equal(S1, mSI)  THEN
                  WriteString ("Duality FALSE:   V[");
                  WriteInt(i, 1);  WriteString ("].W["); WriteInt(j, 1);
                  WriteString ("]"); WriteLn;
                  RETURN FALSE;
                  END
               END
            END 
         END
      END;
   WriteString ("Duality OK"); WriteLn;
   RETURN TRUE;   
   END CheckDuality;

(**************************************************************************)

PROCEDURE BaseEquivalence (B1, B2 : Basis) : BOOLEAN;
   VAR
      i, j, d : BDim;
      VX, WX : BVect;
      ix : BDim;
   BEGIN
   d := B1^.Dim;
   IF  d # B2^.Dim  THEN
      WriteString('BaseEquivalence:  Unequal Dimensions'); WriteLn;
      RETURN FALSE
      END;
   BCreateVect (VX, 0, d);
   BCreateVect (WX, 0, d);
   FOR  i := 1  TO  d  DO
      FOR  j := 1  TO  d  DO
         WITH  B1^  DO
            FOR  ix := 1  TO  d  DO
               VX[ix] := V[i,ix]
               END
            END;
         WITH  B2^  DO
            FOR  ix := 1  TO  d  DO
               WX[ix] := W[j,ix]
               END
            END;
         BProdScalSI (VX, WX, d, S1);
         Divide(S1, B2^.mSI, S2, S1);
         IF  NOT Zero(S1)  THEN
            WriteString('Bases are not equivalent:  V1[');
            WriteInt(i, 1);  WriteString ("].W2["); WriteInt(j, 1);
            WriteString ("]"); WriteLn;
            RETURN FALSE
            END;
         WITH  B2^  DO
            FOR  ix := 1  TO  d  DO
               VX[ix] := V[i,ix]
               END
            END;
         WITH  B1^  DO
            FOR  ix := 1  TO  d  DO
               WX[ix] := W[j,ix]
               END
            END;
         BProdScalSI (VX, WX, d, S1);
         Divide(S1, B1^.mSI, S2, S1);
         IF  NOT Zero(S1)  THEN
            WriteString('Bases are not equivalent:  V2[');
            WriteInt(i, 1);  WriteString ("].W1["); WriteInt(j, 1);
            WriteString ("]"); WriteLn;
            RETURN FALSE
            END
         END
      END;
   BDeleteVect (VX, 0, d);
   BDeleteVect (WX, 0, d);
   RETURN TRUE
   END BaseEquivalence;

(**************************************************************************)
(*
PROCEDURE TriangMatr 
   (M : BMatr;
    d : BDim; 
    e : INTEGER;
    unimod : BOOLEAN);
   (* Le resultat est placee dans la variable globale T.      *)
   (* Si unimod = TRUE cette procedure utilise egalement la   *)
   (* variable globale U. On a UM=T.                          *)
   (* La variable globale signe donne la parite du nombre de  *)
   (* permutations de ligne effectuees.                       *)
   VAR
      i, j, jj, k : BDim;
      nb : CARDINAL;
      eb, numb : INTEGER;
      signe : INTEGER;
      adr  : ADDRESS;
   BEGIN
   signe := 1;
   eb := 15*e;
   IntToSup(1, T[0,0]);
   ShiftLeft(T[0,0], e, T[0,0]);
   BCopyMatr(M, T, d);
   IF  unimod  THEN
      BAffectIdentMatr(U, d)
      END;
   FOR  j := 1  TO  d-1  DO
      nb := 0;
      FOR  i := j  TO  d  DO
         IF  NOT Zero(T[i,j])  THEN
            INC(nb); k := i
            END
         END;
      WHILE  nb > 1  DO
         k := j;
         WHILE  Zero(T[k,j])  DO  INC(k)  END;
         FOR  i := k+1  TO  d  DO
            IF  NOT Zero(T[i,j])  THEN
               IF  AbsSizeOrd(T[k,j], T[i,j]) = -1  THEN
                  k := i
                  END
               END
            END;
         FOR  i := j  TO  d  DO
            IF  (NOT Zero(T[i,j])) AND (i#k) THEN
               BDivideRound(T[i,j], T[k,j], T1);
               ChangeSign(T1, T1);
               FOR  jj := 1  TO  d  DO
                  IF  jj >= j  THEN
                     Multiply(T[k,jj], T1, T2);
                     Add(T[i,jj], T2, T[i,jj]);
                     IF  e > 0  THEN
                        CutLeft(T[i,jj], e, T[i,jj]);
                        numb := NumBits(T[i,jj]);
                        IF  numb = eb  THEN
                           IF  Negative(T[i,jj])  THEN
                              Add(T[0,0], T[i,jj], T[i,jj])
                           ELSE
                              Subtract(T[i,jj], T[0,0], T[i,jj])
                              END
                           END
                        END
                     END;
                  IF  unimod  THEN
                     Multiply(U[k,jj], T1, T2);
                     Add(U[i,jj], T2, U[i,jj]);
                     IF  e > 0  THEN
                        CutLeft(U[i,jj], e, U[i,jj]);
                        numb := NumBits(U[i,jj]);
                        IF  numb = eb  THEN
                           IF  Negative(U[i,jj])  THEN
                              Add(T[0,0], U[i,jj], U[i,jj])
                           ELSE
                              Subtract(U[i,jj], T[0,0], U[i,jj])
                              END
                           END
                        END
                     END
                  END;
               IF  Zero(T[i,j])  THEN  DEC(nb)  END
               END
            END
         END;
      IF  k#j  THEN
         signe := - signe;
         FOR  jj := 1  TO  d  DO
            adr := T[k,jj];
            T[k,jj] := T[j,jj];
            T[j,jj] := adr;
            IF  unimod  THEN
               adr := U[k,jj];
               U[k,jj] := U[j,jj];
               U[j,jj] := adr
               END
            END
         END
      END
   END TriangMatr;
*)
(**************************************************************************)

BEGIN
Create (S1, 2);
Create (S2, 2);
MCreateScal (tempMS);
END LATBASIS.
