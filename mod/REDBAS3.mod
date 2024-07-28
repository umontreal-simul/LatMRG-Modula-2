IMPLEMENTATION MODULE REDBAS3;

FROM SYSTEM   IMPORT ADDRESS;
FROM MYINOUT  IMPORT WriteString, WriteLn;
FROM CHRONO   IMPORT Chrono, TimeUnit, TimeFormat, InitChrono, WriteChrono;

FROM SUPINT   IMPORT SuperInteger, Create, Affect;
FROM SUPCONV  IMPORT SupToInt;
FROM SUPARITH IMPORT Zero, Negative, Smaller, Greater, ChangeSign, AbsSizeOrd,
                     Add, Subtract, Multiply, MultiplyIntSup, Divide;

IMPORT BASIS;
FROM CONFIG   IMPORT BDim;
FROM BASISLR  IMPORT VectLI;
FROM BASISSI  IMPORT BZero, BOne, BScal, BVect, BMatr, BCreateScal, 
                     LIToBScal, BCreateVect, BProdScal, BDivideRound,
                     BCreateMatr, BAffect, BChangeSign, BAdd, BMultiply;
FROM LATBASIS IMPORT Basis;


VAR
   vm            : ARRAY [0..1] OF ARRAY BDim OF BMatr;
   det, det1     : BVect;
   sg            : ARRAY BDim OF BOOLEAN;
   vcurrent      : BASIS.BMatr;
   vzero         : BASIS.BVect;
   g, gmax, g0, g1, g2 : BVect;
   scal1, scal2  : BScal;                  (* Usage local *)
   vect1, vect2, vect3, vect4 : BVect;                    
   T1, T2, T3    : SuperInteger;   
   two           : BScal;
   chr           : Chrono;
   curmaxdim     : BDim;



PROCEDURE TG (B : Basis; d : BDim);
   VAR
      i, j, j1, k, h : BDim;
      adr     : ADDRESS;
   BEGIN
   WITH  B^  DO

      (* Initialisation de vm[1,1] et de vm[0,1].                           *)
      BASIS.BProdScalSI(V[1], V[1], Dim, vm[0,1,1,1]);
      BAffect(BOne, vm[1,1,1,1]);
      sg[0] := TRUE;
      sg[1] := TRUE;
              
      (* Triangulation.                                                     *)
      FOR  k := 2  TO  d  DO
         (* On utilise l'instance precedente.                               *)
         FOR  i := 1  TO  k-1  DO
            FOR  j := 1  TO  k-1  DO
               FOR  h := 0  TO  1  DO
                  BAffect(vm[h,k-1,i,j], vm[h,k,i,j])
                  END
               END
            END;
         sg[k] := sg[k-1];

         (* On met a jour la derniere ligne.                                *)
         FOR  j := 1  TO  k  DO
            BASIS.BProdScalSI(V[k], V[j], Dim, vm[0,k,k,j]);
            BAffect(BZero, vm[1,k,k,j])
            END;
         BAffect(BOne, vm[1,k,k,k]); 
         (* On met a jour la derniere colonne.                              *)
         FOR  i := 1  TO  k-1  DO
            BProdScal(vm[1,k-1,i], vm[0,k,k], k-1, vm[0,k,i,k]);
            BAffect(BZero, vm[1,k,i,k])
            END;
         (* On termine la triangulation.                                    *)
         FOR  i := 1  TO  k-1  DO
            WHILE  (NOT Zero(vm[0,k,i,i])) AND (NOT Zero(vm[0,k,k,i]))  DO
               IF  AbsSizeOrd(vm[0,k,i,i], vm[0,k,k,i]) > -1  THEN
                  BDivideRound(vm[0,k,k,i], vm[0,k,i,i], scal1);
                  BChangeSign(scal1);
                  FOR  j := i  TO  k  DO
                     BMultiply(scal1, vm[0,k,i,j], vm[0,k,0,j]);
                     BAdd(vm[0,k,k,j], vm[0,k,0,j], vm[0,k,k,j])
                     END;
                  FOR  j := 1  TO  k  DO
                     BMultiply(scal1, vm[1,k,i,j], vm[1,k,0,j]);
                     BAdd(vm[1,k,k,j], vm[1,k,0,j], vm[1,k,k,j])
                     END                  
               ELSE
                  BDivideRound(vm[0,k,i,i], vm[0,k,k,i], scal1);
                  BChangeSign(scal1);
                  FOR  j := i  TO  k  DO
                     BMultiply(scal1, vm[0,k,k,j], vm[0,k,0,j]);
                     BAdd(vm[0,k,i,j], vm[0,k,0,j], vm[0,k,i,j])
                     END;
                  FOR  j := 1  TO  k  DO
                     BMultiply(scal1, vm[1,k,k,j], vm[1,k,0,j]);
                     BAdd(vm[1,k,i,j], vm[1,k,0,j], vm[1,k,i,j])
                     END
                  END
               END;
            IF  Zero(vm[0,k,i,i])  THEN
               FOR  j := i  TO  k  DO
                  adr := vm[0,k,i,j];
                  vm[0,k,i,j] := vm[0,k,k,j];
                  vm[0,k,k,j] := adr
                  END;
               FOR  j := 1  TO  k  DO
                  adr := vm[1,k,i,j];
                  vm[1,k,i,j] := vm[1,k,k,j];
                  vm[1,k,k,j] := adr
                  END;
               sg[k] := NOT(sg[k])
               END
            END;
         (* On reduit les entres au dessus de la diagonale a au plus *)
         (* la moitie de la valeur diagonale sur la meme colonne.    *)
         FOR  j := 2  TO  k  DO
            FOR  i := 1  TO  j-1  DO
               BDivideRound (vm[0,k,i,j], vm[0,k,j,j], scal1);
               IF  NOT Zero (scal1)  THEN
                  BChangeSign (scal1);
                  FOR  j1 := j  TO  k  DO
                     BMultiply (scal1, vm[0,k,j,j1], vm[0,k,0,j1]);
                     BAdd (vm[0,k,i,j1], vm[0,k,0,j1], vm[0,k,i,j1])
                     END;
                  FOR  j1 := 1  TO  k  DO
                     BMultiply (scal1, vm[1,k,j,j1], vm[1,k,0,j1]);
                     BAdd (vm[1,k,i,j1], vm[1,k,0,j1], vm[1,k,i,j1])
                     END
                  END
               END
            END
         END;

      FOR  k := 1  TO  d  DO
         BAffect(BOne, det1[k]);
         FOR  i := 1  TO  k-1  DO
            Multiply(vm[0,k,i,i], det1[k], det1[k])
            END;
         Multiply(vm[0,k,k,k], det1[k], det[k]);
         Multiply(det1[k], two, det1[k]);
         IF  NOT(sg[k])  THEN
            ChangeSign(det[k], det[k])
            END
         END
      END
   END TG;

PROCEDURE TGD (B : Basis; d : BDim);
   VAR
      i, j, j1, k, dim, h : BDim;
      adr     : ADDRESS;
   BEGIN
WriteString('TGD');
WriteLn;
InitChrono(chr);
   WITH  B^  DO
      
      (* Initialisation de vm[1,1] et de vm[0,1].                           *)
      BASIS.BProdScalSI(W[Dim], W[Dim], Dim, vm[0,Dim,1,1]);
      BAffect(BOne, vm[1,Dim,1,1]);
      sg[Dim+1] := TRUE;
      sg[Dim] := TRUE;

      (* Triangulation.                                                     *)
      FOR  k := Dim-1 TO  d+1  BY  -1  DO
         (* Dimension courante.                                             *)
         dim := Dim-k+1;
         (* On utilise l'instance precedente.                               *)
         FOR  i := 1  TO  dim-1  DO
            FOR  j := 1  TO  dim-1  DO
               FOR  h := 0  TO  1  DO
                  BAffect(vm[h,k+1,i,j], vm[h,k,i,j])
                  END
               END
            END;
         sg[k] := sg[k+1];

         (* On met a jour la derniere ligne.                                *)
         FOR  j := 1  TO  dim  DO
            BASIS.BProdScalSI(W[k], W[Dim-j+1], Dim, vm[0,k,dim,j]);
            BAffect(BZero, vm[1,k,dim,j])
            END;
         BAffect(BOne, vm[1,k,dim,dim]);
         (* On met a jour la derniere colonne.                              *)
         FOR  i := 1  TO  dim-1  DO
            BProdScal(vm[1,k+1,i], vm[0,k,dim], dim-1, vm[0,k,i,dim]);
            BAffect(BZero, vm[1,k,i,dim])
            END;

         (* On termine la triangulation.                                    *)
         FOR  i := 1  TO  dim-1  DO
            WHILE  (NOT Zero(vm[0,k,i,i])) AND (NOT Zero(vm[0,k,dim,i]))  DO
               IF  AbsSizeOrd(vm[0,k,i,i], vm[0,k,dim,i]) > -1  THEN
                  BDivideRound(vm[0,k,dim,i], vm[0,k,i,i], scal1);
                  BChangeSign(scal1);
                  FOR  j := i  TO  dim  DO
                     BMultiply(scal1, vm[0,k,i,j], vm[0,k,0,j]);
                     BAdd(vm[0,k,dim,j], vm[0,k,0,j], vm[0,k,dim,j])
                     END;
                  FOR  j := 1  TO  dim  DO
                     BMultiply(scal1, vm[1,k,i,j], vm[1,k,0,j]);
                     BAdd(vm[1,k,dim,j], vm[1,k,0,j], vm[1,k,dim,j])
                     END
               ELSE
                  BDivideRound(vm[0,k,i,i], vm[0,k,dim,i], scal1);
                  BChangeSign(scal1);
                  FOR  j := i  TO  dim  DO
                     BMultiply(scal1, vm[0,k,dim,j], vm[0,k,0,j]);
                     BAdd(vm[0,k,i,j], vm[0,k,0,j], vm[0,k,i,j])
                     END;
                  FOR  j := 1  TO  dim  DO
                     BMultiply(scal1, vm[1,k,dim,j], vm[1,k,0,j]);
                     BAdd(vm[1,k,i,j], vm[1,k,0,j], vm[1,k,i,j])
                     END
                  END
               END;
            IF  Zero(vm[0,k,i,i])  THEN
               FOR  j := i  TO  dim  DO
                  adr := vm[0,k,i,j];
                  vm[0,k,i,j] := vm[0,k,dim,j];
                  vm[0,k,dim,j] := adr
                  END;
               FOR  j := 1  TO  dim  DO
                  adr := vm[1,k,i,j];
                  vm[1,k,i,j] := vm[1,k,dim,j];
                  vm[1,k,dim,j] := adr
                  END;
               sg[k] := NOT(sg[k])
               END
            END;
         (* On reduit les entres au dessus de la diagonale a au plus *)
         (* la moitie de la valeur diagonale sur la meme colonne.    *)
         FOR  j := 2  TO  dim  DO
            FOR  i := 1  TO  j-1  DO
               BDivideRound (vm[0,k,i,j], vm[0,k,j,j], scal1);
               IF  NOT Zero (scal1)  THEN
                  BChangeSign (scal1);
                  FOR  j1 := j  TO  dim  DO
                     BMultiply (scal1, vm[0,k,j,j1], vm[0,k,0,j1]);
                     BAdd (vm[0,k,i,j1], vm[0,k,0,j1], vm[0,k,i,j1])
                     END;
                  FOR  j1 := 1  TO  dim  DO
                     BMultiply (scal1, vm[1,k,j,j1], vm[1,k,0,j1]);
                     BAdd (vm[1,k,i,j1], vm[1,k,0,j1], vm[1,k,i,j1])
                     END
                  END
               END
            END
         END;

      FOR  k := Dim  TO  d+1  BY  -1  DO
         dim := Dim-k+1;
         BAffect(BOne, det1[k]);
         FOR  i := 1  TO  dim-1  DO
            Multiply(vm[0,k,i,i], det1[k], det1[k])
            END;
         Multiply(vm[0,k,dim,dim], det1[k], det[k]);
         IF  NOT(sg[k])  THEN
            ChangeSign(det[k], det[k])
            END
         END
      END;
WriteChrono(chr, sec);
WriteLn
   END TGD;

(* ajmal 15 Nov 1996 *)
   PROCEDURE VerifZ0
      ( B                    : Basis;
        j                    : BDim;
        VAR d2               : BDim;
        VAR kprime, kprime1  : BDim;
        VAR FoundZero, signe : BOOLEAN;
        VAR adr              : ADDRESS;
        VAR z                : VectLI ) : BOOLEAN;

   (* Retourne FALSE si on trouve un vecteur plus court.                    *)

      VAR
         zinit : LONGINT;
         high, central, in : BOOLEAN;
         k, k1: BDim;
      BEGIN
      k := kprime;
      k1 := kprime1;
      WITH  B^  DO
         (* Initialisation de vcurrent.                                     *)
         BASIS.BCopyVect(vcurrent[j+1], vcurrent[j], Dim);
        
         (*-----------------------------------------------------------------*)

         (* Calcul des coefficients de notre fonction quadratique.          *)
         
         IF  j <= d2  THEN
            (* Premier coefficient: G(v1,...,vj-1,vcurrent).                *)
            (* Derniere colonne. Derniere ligne.                            *)
            FOR  k := 1  TO  j-1  DO
               BASIS.BProdScalSI(V[k], vcurrent[j], Dim, vect1[k]);
               BAffect(vect1[k], vect2[k]);
               (* En vue du deuxieme coefficient. *)
               BAffect(vect1[k], vect4[k])
               END;
            BASIS.BProdScalSI(vcurrent[j], vcurrent[j], Dim, vect2[j]);
         
            (* On termine la triangulation.                                 *)
            signe := sg[j-1];
            BAffect(BOne, g0[j]);
            FOR  k := 1  TO  j-1  DO
               FOR  k1 := k  TO  j-1  DO
                  BAffect(vm[0,j-1,k,k1], vect3[k1])
                  END;
               (* Mise a jour de la derniere colonne.                       *)
               BProdScal(vm[1,j-1,k], vect1, j-1, vect3[j]);

               WHILE  (NOT Zero(vect3[k])) AND (NOT Zero(vect2[k]))  DO
                  IF  AbsSizeOrd(vect3[k], vect2[k]) > -1  THEN
                     BDivideRound(vect2[k], vect3[k], scal1);
                     BChangeSign(scal1);
                     FOR  k1 := k  TO  j  DO
                        BMultiply(vect3[k1], scal1, vect3[0]);
                        BAdd(vect2[k1], vect3[0], vect2[k1])
                        END
                  ELSE
                     BDivideRound(vect3[k], vect2[k], scal1);
                     BChangeSign(scal1);
                     FOR  k1 := k  TO  j  DO
                        BMultiply(vect2[k1], scal1, vect2[0]);
                        BAdd(vect3[k1], vect2[0], vect3[k1])
                        END
                     END
                  END;
               IF  Zero(vect3[k])  THEN
                  FOR  k1 := k  TO  j  DO
                     adr := vect3[k1];
                     vect3[k1] := vect2[k1];
                     vect2[k1] := adr
                     END;
                  signe := NOT signe
                  END;
               BMultiply(g0[j], vect3[k], g0[j])
               END;
            BMultiply(g0[j], vect2[j], g0[j]);
            IF  NOT signe  THEN
               BChangeSign(g0[j])
               END;

            (* Deuxieme coefficient (multiplie par 2).                      *)
            BASIS.BProdScalSI(V[j], vcurrent[j], Dim, vect4[j]);
            BProdScal(vm[1,j,j], vect4, j, g1[j]);
            BMultiply(g1[j], det1[j], g1[j]);
            IF  NOT sg[j]  THEN
               BChangeSign(g1[j])
               END;
 
            (* Troisieme coefficient: G(v1,...,vj) = det(j).                *)
            Affect(det[j], g2[j])

         ELSE (*  j > d2  *)
            (* Premier coefficient: g0[j] = det(j)|vcurrent|^2              *)
            (*                         - G(wn,...,wj,vcurrent).             *)
            (* On calcule d'abord G(wn,...,wj,vcurrent).                    *)
            (* Derniere ligne.                                              *)
            FOR  k := 1  TO  Dim-j+1  DO
               BASIS.BProdScalSI(W[Dim-k+1], vcurrent[j], Dim, vect1[k]);
               BAffect(vect1[k], vect2[k])
               END;
            BASIS.BProdScalSI(vcurrent[j], vcurrent[j], Dim, vect2[Dim-j+2]);

            (* On calcule det(j)|vcurrent|^2                                *)
            Affect(vect2[Dim-j+2], scal2);
            Multiply(scal2, det[j], scal2);

            (* On termine la triangulation.                                 *)
            signe := sg[j];
            BAffect(BOne, g0[j]);
            FOR  k := 1  TO  Dim-j+1  DO
               FOR  k1 := k  TO  Dim-j+1  DO
                  BAffect(vm[0,j,k,k1], vect3[k1])
                  END;  

               (* Mise a jour de la derniere position de la k-ieme ligne.   *)
               BProdScal(vm[1,j,k], vect1, Dim-j+1, vect3[Dim-j+2]);
               (* En vue du deuxieme coefficient.                           *)
               IF  k = Dim-j+1  THEN
                  Affect(vect3[Dim-j+2], vect4[Dim-j+1])
                  END;

               WHILE  (NOT Zero(vect3[k])) AND (NOT Zero(vect2[k]))  DO
                  IF  AbsSizeOrd(vect3[k], vect2[k]) > -1  THEN
                     BDivideRound(vect2[k], vect3[k], scal1);
                     BChangeSign(scal1);
                     FOR  k1 := k  TO  Dim-j+2  DO
                        BMultiply(vect3[k1], scal1, vect3[0]);
                        BAdd(vect2[k1], vect3[0], vect2[k1])
                        END
                  ELSE
                     BDivideRound(vect3[k], vect2[k], scal1);
                     BChangeSign(scal1);
                     FOR  k1 := k  TO  Dim-j+2  DO
                        BMultiply(vect2[k1], scal1, vect2[0]);
                        BAdd(vect3[k1], vect2[0], vect3[k1])
                        END
                     END
                  END;
               IF  Zero(vect3[k])  THEN
                  FOR  k1 := k  TO  Dim-j+2  DO
                     adr := vect3[k1];
                     vect3[k1] := vect2[k1];
                     vect2[k1] := adr
                     END;
                  signe := NOT signe
                  END;
               BMultiply(g0[j], vect3[k], g0[j])
               END;
            Multiply(g0[j], vect2[Dim-j+2], g0[j]);
            IF  NOT signe  THEN
               ChangeSign(g0[j], g0[j])
               END;
            ChangeSign(g0[j], g0[j]);

            Add(scal2, g0[j], g0[j]);

            (* Deuxieme coefficient.                                        *)
            BASIS.BProdScalSI(V[j], vcurrent[j], Dim, vect4[Dim-j+2]);
            Multiply(vm[0,j,Dim-j+1,Dim-j+1], vect4[Dim-j+2], g1[j]);
            Multiply(mSI, vect4[Dim-j+1], scal2);
            Subtract(g1[j], scal2, g1[j]);
            Multiply(g1[j], det1[j], g1[j]);
            IF  sg[j]  THEN
               ChangeSign(g1[j], g1[j])
               END;
            Multiply(vect4[Dim-j+2], det[j], scal2);
            Add(scal2, g1[j], g1[j]);
            Multiply(two, g1[j], g1[j]);

            (* Troisieme coefficient.                                       *)
            BASIS.BProdScalSI(V[j], V[j], Dim, scal1);
            Multiply(vm[0,j,Dim-j+1,Dim-j+1], scal1, g2[j]); 
            Multiply(vm[1,j,Dim-j+1,Dim-j+1], mSI, scal2);
            Multiply(mSI, scal2, scal2);
            Subtract(g2[j], scal2, g2[j]);
            Multiply(det1[j], g2[j], g2[j]);
            IF  sg[j]  THEN
               ChangeSign(g2[j], g2[j])
               END;

            Multiply(scal1, det[j], scal1);
            Add(scal1, g2[j], g2[j])
            END;

         (*******************************************************************)

         IF  NOT FoundZero  THEN
            IF  j > 1  THEN
               zinit := 0
            ELSE
               zinit := -1;
               FoundZero := TRUE
               END;
           high := FALSE
         ELSE
            (* Calcul de zinit.                                             *)
            Multiply(two, g2[j], T1);
            Divide(g1[j], T1, T2, T3);
            IF  Zero(T3)  THEN
               central := TRUE
            ELSE
               central := FALSE
               END;
            SupToInt(T2, zinit);
            zinit := -zinit;
            IF  NOT(central) AND Negative(g1[j])  THEN
               INC(zinit)
               END;
            high := TRUE
            END;

         (* Initialisation de z[j].                                         *)
         z[j] := zinit;
         
         (* Mise a jour de vcurrent.                                        *)
         BASIS.BModifVectLI(vcurrent[j], V[j], zinit, Dim);

         (* Calcul de g[j] = g2 z^2 + g1 z + g0 (z = zinit).                *)
         MultiplyIntSup(zinit, g2[j], g[j]);
         Add(g[j], g1[j], g[j]);
         MultiplyIntSup(zinit, g[j], g[j]);
         Add(g[j], g0[j], g[j]);

         REPEAT
            REPEAT
               in :=  Smaller(g[j], gmax[j]);
               IF  in  THEN
(* ajmal 15 Nov 1996                                                        *)
(*                  IF  ((j = 1) OR ((j > 1) AND (NOT VerifZ0(j-1))))  THEN *)
                  IF  ((j = 1) OR ((j > 1) AND (NOT VerifZ0(B, j-1, d2, k, k1, FoundZero, signe, adr, z ))))  THEN
                     kprime := k;
                     kprime1 := k1;
                     RETURN FALSE
                     END;
                  IF  high  THEN
                     Add(g[j], g1[j], g[j]);
                     MultiplyIntSup((2*z[j]+1), g2[j], scal1);
                     Add(g[j], scal1, g[j]);
                     INC(z[j]);
                     BASIS.BModifVectLI(vcurrent[j], V[j], 1, Dim)
                  ELSE
                     Subtract(g[j], g1[j], g[j]);
                     MultiplyIntSup((2*z[j]-1), g2[j], scal1);
                     Subtract(g[j], scal1, g[j]);
                     DEC(z[j]);
                     BASIS.BModifVectLI(vcurrent[j], V[j], -1, Dim)
                     END
                  END
            UNTIL  NOT(in);
            IF  high  THEN
               MultiplyIntSup(zinit-1, g2[j], g[j]);
               Add(g[j], g1[j], g[j]);
               MultiplyIntSup(zinit-1, g[j], g[j]);
               Add(g[j], g0[j], g[j]);
               BASIS.BModifVectLI(vcurrent[j], V[j], zinit-1-z[j], Dim);
               z[j] := zinit - 1
               END; 
            high := NOT high
         UNTIL high
         END;
(* ajmal 191196 *)
(* WriteString("DDD"); WriteLn; *)
      kprime := k;
      kprime1 := k1;

      RETURN TRUE
      END VerifZ0;      

(*-----------------------------------------*)

PROCEDURE InitREDBAS3 (d2 : BDim);
   VAR
      i, d1 : BDim;
   BEGIN
   IF  d2 > curmaxdim  THEN
      IF  curmaxdim = 0  THEN  d1 := 0  ELSE  d1 := curmaxdim + 1  END;
      FOR  i := d1  TO  d2  DO
         BCreateMatr(vm[0,i], 0, i); BCreateMatr(vm[1,i], 0, i)
         END;
      BCreateVect(det, d1, d2);
      BCreateVect(det1, d1, d2);
      BCreateVect(g, d1, d2);
      BCreateVect(g0, d1, d2);
      BCreateVect(g1, d1, d2);
      BCreateVect(g2, d1, d2);
      BCreateVect(gmax, d1, d2);
      BASIS.BCreateMatr(vcurrent, d1, d2);
      BCreateVect(vect1, d1, d2);
      BCreateVect(vect2, d1, d2);
      BCreateVect(vect3, d1, d2);
      BCreateVect(vect4, d1, d2);
      BASIS.BCreateVect(vzero, d1, d2);
      FOR  i := d1  TO  d2  DO
         BASIS.BAffect(BASIS.BZero, vzero[i])
         END
      END   
   END InitREDBAS3;

(*-----------------------------------------*)

PROCEDURE VerifShortest (B : Basis; d1, d2 : BDim; VAR z : VectLI) : BOOLEAN;
   (* On doit avoir d1 ou d2 = Dim.                                 *)
   (* Si d1 = Dim, retourne TRUE lorsque le premier vecteur de la   *)
   (* base est un plus petit vecteur dans le reseau. Utilise TG     *)
   (* pour le calcul des valeurs admissibles de zj si j <= d2 et    *)
   (* sinon utilise TGD.                                            *)
   (* Si d2 = Dim, retourne TRUE lorsque le premier vecteur de la   *)
   (* base est le plus petit vecteur du reseau engendre par les d1  *)
   (* premiers vecteurs de la base.                                 *)
   VAR
      k, k1 : BDim;
      FoundZero, signe : BOOLEAN;
      adr : ADDRESS;

(* deplace a l'exterieur - ajmal 15 Nov 1996
   PROCEDURE VerifZ0 (j : BDim) : BOOLEAN;

      VAR
         zinit : LONGINT;
         high, central, in : BOOLEAN;
      BEGIN
      WITH  B^  DO
         BASIS.BCopyVect(vcurrent[j+1], vcurrent[j], Dim);
                 
         IF  j <= d2  THEN
            FOR  k := 1  TO  j-1  DO
               BASIS.BProdScalSI(V[k], vcurrent[j], Dim, vect1[k]);
               BAffect(vect1[k], vect2[k]);
               BAffect(vect1[k], vect4[k])
               END;
            BASIS.BProdScalSI(vcurrent[j], vcurrent[j], Dim, vect2[j]);
         
            signe := sg[j-1];
            BAffect(BOne, g0[j]);
            FOR  k := 1  TO  j-1  DO
               FOR  k1 := k  TO  j-1  DO
                  BAffect(vm[0,j-1,k,k1], vect3[k1])
                  END;
               BProdScal(vm[1,j-1,k], vect1, j-1, vect3[j]);

               WHILE  (NOT Zero(vect3[k])) AND (NOT Zero(vect2[k]))  DO
                  IF  AbsSizeOrd(vect3[k], vect2[k]) > -1  THEN
                     BDivideRound(vect2[k], vect3[k], scal1);
                     BChangeSign(scal1);
                     FOR  k1 := k  TO  j  DO
                        BMultiply(vect3[k1], scal1, vect3[0]);
                        BAdd(vect2[k1], vect3[0], vect2[k1])
                        END
                  ELSE
                     BDivideRound(vect3[k], vect2[k], scal1);
                     BChangeSign(scal1);
                     FOR  k1 := k  TO  j  DO
                        BMultiply(vect2[k1], scal1, vect2[0]);
                        BAdd(vect3[k1], vect2[0], vect3[k1])
                        END
                     END
                  END;
               IF  Zero(vect3[k])  THEN
                  FOR  k1 := k  TO  j  DO
                     adr := vect3[k1];
                     vect3[k1] := vect2[k1];
                     vect2[k1] := adr
                     END;
                  signe := NOT signe
                  END;
               BMultiply(g0[j], vect3[k], g0[j])
               END;
            BMultiply(g0[j], vect2[j], g0[j]);
            IF  NOT signe  THEN
               BChangeSign(g0[j])
               END;

            BASIS.BProdScalSI(V[j], vcurrent[j], Dim, vect4[j]);
            BProdScal(vm[1,j,j], vect4, j, g1[j]);
            BMultiply(g1[j], det1[j], g1[j]);
            IF  NOT sg[j]  THEN
               BChangeSign(g1[j])
               END;
 
            Affect(det[j], g2[j])

         ELSE
            FOR  k := 1  TO  Dim-j+1  DO
               BASIS.BProdScalSI(W[Dim-k+1], vcurrent[j], Dim, vect1[k]);
               BAffect(vect1[k], vect2[k])
               END;
            BASIS.BProdScalSI(vcurrent[j], vcurrent[j], Dim, vect2[Dim-j+2]);

            Affect(vect2[Dim-j+2], scal2);
            Multiply(scal2, det[j], scal2);

            signe := sg[j];
            BAffect(BOne, g0[j]);
            FOR  k := 1  TO  Dim-j+1  DO
               FOR  k1 := k  TO  Dim-j+1  DO
                  BAffect(vm[0,j,k,k1], vect3[k1])
                  END;  

               BProdScal(vm[1,j,k], vect1, Dim-j+1, vect3[Dim-j+2]);
               IF  k = Dim-j+1  THEN
                  Affect(vect3[Dim-j+2], vect4[Dim-j+1])
                  END;

               WHILE  (NOT Zero(vect3[k])) AND (NOT Zero(vect2[k]))  DO
                  IF  AbsSizeOrd(vect3[k], vect2[k]) > -1  THEN
                     BDivideRound(vect2[k], vect3[k], scal1);
                     BChangeSign(scal1);
                     FOR  k1 := k  TO  Dim-j+2  DO
                        BMultiply(vect3[k1], scal1, vect3[0]);
                        BAdd(vect2[k1], vect3[0], vect2[k1])
                        END
                  ELSE
                     BDivideRound(vect3[k], vect2[k], scal1);
                     BChangeSign(scal1);
                     FOR  k1 := k  TO  Dim-j+2  DO
                        BMultiply(vect2[k1], scal1, vect2[0]);
                        BAdd(vect3[k1], vect2[0], vect3[k1])
                        END
                     END
                  END;
               IF  Zero(vect3[k])  THEN
                  FOR  k1 := k  TO  Dim-j+2  DO
                     adr := vect3[k1];
                     vect3[k1] := vect2[k1];
                     vect2[k1] := adr
                     END;
                  signe := NOT signe
                  END;
               BMultiply(g0[j], vect3[k], g0[j])
               END;
            Multiply(g0[j], vect2[Dim-j+2], g0[j]);
            IF  NOT signe  THEN
               ChangeSign(g0[j], g0[j])
               END;
            ChangeSign(g0[j], g0[j]);

            Add(scal2, g0[j], g0[j]);

            BASIS.BProdScalSI(V[j], vcurrent[j], Dim, vect4[Dim-j+2]);
            Multiply(vm[0,j,Dim-j+1,Dim-j+1], vect4[Dim-j+2], g1[j]);
            Multiply(mSI, vect4[Dim-j+1], scal2);
            Subtract(g1[j], scal2, g1[j]);
            Multiply(g1[j], det1[j], g1[j]);
            IF  sg[j]  THEN
               ChangeSign(g1[j], g1[j])
               END;
            Multiply(vect4[Dim-j+2], det[j], scal2);
            Add(scal2, g1[j], g1[j]);
            Multiply(two, g1[j], g1[j]);

            BASIS.BProdScalSI(V[j], V[j], Dim, scal1);
            Multiply(vm[0,j,Dim-j+1,Dim-j+1], scal1, g2[j]); 
            Multiply(vm[1,j,Dim-j+1,Dim-j+1], mSI, scal2);
            Multiply(mSI, scal2, scal2);
            Subtract(g2[j], scal2, g2[j]);
            Multiply(det1[j], g2[j], g2[j]);
            IF  sg[j]  THEN
               ChangeSign(g2[j], g2[j])
               END;
            Multiply(scal1, det[j], scal1);
            Add(scal1, g2[j], g2[j])
            END;

         IF  NOT FoundZero  THEN
            IF  j > 1  THEN
               zinit := 0
            ELSE
               zinit := -1;
               FoundZero := TRUE
               END;
           high := FALSE
         ELSE
            Multiply(two, g2[j], T1);
            Divide(g1[j], T1, T2, T3);
            IF  Zero(T3)  THEN
               central := TRUE
            ELSE
               central := FALSE
               END;
            SupToInt(T2, zinit);
            zinit := -zinit;
            IF  NOT(central) AND Negative(g1[j])  THEN
               INC(zinit)
               END;
            high := TRUE
            END;

         z[j] := zinit;
         
         BASIS.BModifVectLI(vcurrent[j], V[j], zinit, Dim);

         MultiplyIntSup(zinit, g2[j], g[j]);
         Add(g[j], g1[j], g[j]);
         MultiplyIntSup(zinit, g[j], g[j]);
         Add(g[j], g0[j], g[j]);

         REPEAT
            REPEAT
               in :=  Smaller(g[j], gmax[j]);
               IF  in  THEN         
                  IF  ((j = 1) OR ((j > 1) AND (NOT VerifZ0(j-1))))  THEN
                     RETURN FALSE
                     END;
                  IF  high  THEN
                     Add(g[j], g1[j], g[j]);
                     MultiplyIntSup((2*z[j]+1), g2[j], scal1);
                     Add(g[j], scal1, g[j]);
                     INC(z[j]);
                     BASIS.BModifVectLI(vcurrent[j], V[j], 1, Dim)
                  ELSE
                     Subtract(g[j], g1[j], g[j]);
                     MultiplyIntSup((2*z[j]-1), g2[j], scal1);
                     Subtract(g[j], scal1, g[j]);
                     DEC(z[j]);
                     BASIS.BModifVectLI(vcurrent[j], V[j], -1, Dim)
                     END
                  END
            UNTIL  NOT(in);
            IF  high  THEN
               MultiplyIntSup(zinit-1, g2[j], g[j]);
               Add(g[j], g1[j], g[j]);
               MultiplyIntSup(zinit-1, g[j], g[j]);
               Add(g[j], g0[j], g[j]);
               BASIS.BModifVectLI(vcurrent[j], V[j], zinit-1-z[j], Dim);
               z[j] := zinit - 1
               END; 
            high := NOT high
         UNTIL high
         END;
      RETURN TRUE
      END VerifZ0;      
End ajmal *)

   BEGIN

   WITH  B^  DO

      InitREDBAS3(Dim);

      IF  d1 = Dim  THEN
         TG(B, d2); TGD(B, d2)
      ELSE
         TG(B, d1)
         END;

      BASIS.BProdScalSI(V[1], V[1], Dim, gmax[1]);

      IF  d1 = Dim  THEN 
         FOR  k := 2  TO  d2  DO
            Multiply(det[k-1], gmax[1], gmax[k])
            END;
         FOR  k := Dim  TO  d2+1  BY  -1  DO
            Multiply(det[k], gmax[1], gmax[k])
            END
      ELSE
         FOR  k := 2  TO  d1  DO
            Multiply(det[k-1], gmax[1], gmax[k])
            END;
         FOR  k := d1+1  TO  Dim  DO
            z[k] := 0
            END
         END;

      BASIS.BCopyVect(vzero, vcurrent[d1+1], Dim);      
      FoundZero := FALSE;
(* ajmal 15 Nov 1996        *)
(*      RETURN  VerifZ0(d1) *)
      RETURN  VerifZ0(B, d1, d2, k, k1, FoundZero, signe, adr, z )
      END
   END VerifShortest;


PROCEDURE VerifMinkowski (B : Basis;  d : BDim) : BOOLEAN;
   BEGIN
   WriteLn;
   WriteString ("Sorry, REDBAS3.VerifMinkowski not implemented yet.");
   WriteLn;  
   WriteLn;  
   HALT;
   RETURN FALSE; (* retour bidon pour satisfaire le compilateur *)
   END  VerifMinkowski;




BEGIN
curmaxdim := 0;
BCreateScal(two);
LIToBScal(2, two);
BCreateScal(scal1);
BCreateScal(scal2);
Create(T1, 0); Create(T2, 0); Create(T3, 0);
END REDBAS3.
