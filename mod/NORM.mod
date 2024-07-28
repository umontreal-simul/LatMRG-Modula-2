IMPLEMENTATION MODULE NORM;

FROM Storage  IMPORT ALLOCATE, DEALLOCATE;
FROM MYINOUT  IMPORT WriteLn, WriteString, Assert;
FROM NUM      IMPORT Pi, e, IToLR, WriteLR, WriteLI, StringToLR, TwoExp,
                     Pow, Lg, Ln, Sqrt, Exp;
FROM NUM2     IMPORT Factorielle;
FROM MYSTR    IMPORT Copy;
IMPORT BASISLR;
FROM BASISLR  IMPORT BVect;
FROM CONFIG   IMPORT MDim, BDim;
FROM MULT     IMPORT MScal, MScalToLR, MWriteScal;

CONST
   MaxtBestLat   = 48;
   MaxtLaminated = 48;
   MaxtMinkowski = 48;
   MaxtRogers    = 48;
   MaxtMinkL1    = 48;

VAR
   GamBestLat,
   GamLaminated,
   GamMinkowski,
   GamRogers,
   GamMinkL1   : BASISLR.BVect;

(*-------------------------------------------------------------------------*)

PROCEDURE CreateNormaliz (VAR G : Normaliz);
   BEGIN
   NEW (G); 
   END CreateNormaliz;

PROCEDURE DeleteNormaliz (VAR G : Normaliz);
   BEGIN
   DISPOSE (G)
   END DeleteNormaliz;

(*-------------------------------------------------------------------------*)

PROCEDURE CalcBestLat ();
   (* Was used to compute the constants for the procedure InitBestLat.     *)
   (* Puts these constants in GamBestLat.                                  *)
   VAR
      i : INTEGER;
      DeltaBestLat : BVect;
      x : LONGREAL;
   BEGIN
   DeltaBestLat [ 1] := 1.0 / 2.0;
   DeltaBestLat [ 2] := 1.0 / (2.0 * Sqrt(3.0));
   DeltaBestLat [ 3] := 1.0 / (4.0 * Sqrt(2.0));
   DeltaBestLat [ 4] := 1.0 / 8.0;
   DeltaBestLat [ 5] := 1.0 / (8.0 * Sqrt(2.0));
   DeltaBestLat [ 6] := 1.0 / (8.0 * Sqrt(3.0));
   DeltaBestLat [ 7] := 1.0 / 16.0;
   DeltaBestLat [ 8] := 1.0 / 16.0;
   DeltaBestLat [ 9] := 1.0 / (16.0 * Sqrt(2.0));
   DeltaBestLat [10] := 1.0 / (16.0 * Sqrt(3.0));
   DeltaBestLat [11] := 1.0 / (18.0 * Sqrt(3.0));
   DeltaBestLat [12] := 1.0 / 27.0;
   DeltaBestLat [13] := 1.0 / (18.0 * Sqrt(3.0));
   DeltaBestLat [14] := 1.0 / (16.0 * Sqrt(3.0));
   DeltaBestLat [15] := 1.0 / (16.0 * Sqrt(2.0));
   DeltaBestLat [16] := 1.0 / 16.0;
   DeltaBestLat [17] := 1.0 / 16.0;
   DeltaBestLat [18] := 1.0 / (8.0 * Sqrt(3.0));
   DeltaBestLat [19] := 1.0 / (8.0 * Sqrt(2.0));
   DeltaBestLat [20] := 1.0 / 8.0;
   DeltaBestLat [21] := 1.0 / (4.0 * Sqrt(2.0));
   DeltaBestLat [22] := 1.0 / (2.0 * Sqrt(3.0));
   DeltaBestLat [23] := 0.5;
   DeltaBestLat [24] := 1.0;
   DeltaBestLat [25] := 1.0 / Sqrt(2.0);
   DeltaBestLat [26] := 1.0 / Sqrt(3.0);
   DeltaBestLat [27] := 1.0 / Sqrt(3.0);
   DeltaBestLat [28] := 2.0 / 3.0;
   DeltaBestLat [29] := 1.0 / Sqrt(3.0);
   DeltaBestLat [30] := Pow (3.0, 13.5) / TwoExp[22];
   DeltaBestLat [31] := Pow (3.0, 15.0) / Pow (2.0, 23.5);
   DeltaBestLat [32] := Pow (3.0, 16.0) / TwoExp[24];
   DeltaBestLat [33] := Pow (3.0, 16.5) / TwoExp[25];
   DeltaBestLat [34] := Pow (3.0, 16.5) / TwoExp[25];
   DeltaBestLat [35] := 2.0 * Sqrt(2.0);
   DeltaBestLat [36] := TwoExp[18] / Pow (3.0, 10.0);
   DeltaBestLat [37] := 4.0 / Sqrt(2.0);
   DeltaBestLat [38] := 8.0;
   DeltaBestLat [39] := Pow (3.0, 16.0) / (TwoExp[20] * Sqrt(14.0));
   DeltaBestLat [40] := Pow (3.0, 17.0) / Pow (2.0, 22.5);
   DeltaBestLat [41] := Pow (3.0, 17.0) / Pow (2.0, 21.5);
   DeltaBestLat [42] := Pow (3.0, 18.0) / TwoExp[22];
   DeltaBestLat [43] := Pow (3.0, 19.0) / Pow (2.0, 22.5);
   DeltaBestLat [44] := Pow (3.0, 20.0) / TwoExp[23];
   DeltaBestLat [45] := Pow (3.0, 21.0) / Pow (2.0, 23.5);
   DeltaBestLat [46] := Pow (3.0, 21.5) / TwoExp[23];
   DeltaBestLat [47] := Pow (3.0, 23.0) / TwoExp[24];
   DeltaBestLat [48] := Pow (3.0, 24.0) / TwoExp[24];
   FOR i := 1 TO MaxtBestLat DO
      x := 2.0 * Pow (DeltaBestLat[i], 1.0/(IToLR(i)));
      GamBestLat[i] := x * x;
      END;
   END CalcBestLat;


PROCEDURE InitBestLat (VAR GamBestLat : BVect);
   BEGIN
   GamBestLat [ 0] :=     0.00000000000000 ;
   GamBestLat [ 1] :=     1.00000000000000 ;
   GamBestLat [ 2] :=     1.15470053837925 ;
   GamBestLat [ 3] :=     1.25992104989487 ;
   GamBestLat [ 4] :=     1.41421356237309 ;
   GamBestLat [ 5] :=     1.51571656651040 ;
   GamBestLat [ 6] :=     1.66536635531121 ;
   GamBestLat [ 7] :=     1.81144732852781 ;
   GamBestLat [ 8] :=     2.00000000000000 ;
   GamBestLat [ 9] :=     2.00000000000000 ;
   GamBestLat [10] :=     2.05837201792952 ;
   GamBestLat [11] :=     2.14019806587100 ;
   GamBestLat [12] :=     2.30940107675850 ;
   GamBestLat [13] :=     2.35634843010647 ;
   GamBestLat [14] :=     2.48864391982238 ;
   GamBestLat [15] :=     2.63901582154579 ;
   GamBestLat [16] :=     2.82842712474619 ;
   GamBestLat [17] :=     2.88668115405991 ;
   GamBestLat [18] :=     2.98682599936104 ;
   GamBestLat [19] :=     3.09851928453331 ;
   GamBestLat [20] :=     3.24900958542494 ;
   GamBestLat [21] :=     3.39145596751014 ;
   GamBestLat [22] :=     3.57278019514216 ;
   GamBestLat [23] :=     3.76602735259556 ;
   GamBestLat [24] :=     4.00000000000000 ;
   GamBestLat [25] :=     3.89061978964914 ;
   GamBestLat [26] :=     3.83450381188673 ;
   GamBestLat [27] :=     3.84050941168887 ;
   GamBestLat [28] :=     3.88581431864262 ;
   GamBestLat [29] :=     3.85130163722559 ;
   GamBestLat [30] :=     3.89007935085599 ;
   GamBestLat [31] :=     4.04939294446075 ;
   GamBestLat [32] :=     4.24264068711928 ;
   GamBestLat [33] :=     4.19831665675995 ;
   GamBestLat [34] :=     4.19234580216893 ;
   GamBestLat [35] :=     4.24485209333349 ;
   GamBestLat [36] :=     4.34532859258359 ;
   GamBestLat [37] :=     4.23124164832276 ;
   GamBestLat [38] :=     4.46263167104618 ;
   GamBestLat [39] :=     4.52280106656485 ;
   GamBestLat [40] :=     4.66610290863847 ;
   GamBestLat [41] :=     4.80847247019275 ;
   GamBestLat [42] :=     4.96199485288772 ;
   GamBestLat [43] :=     5.11293933165865 ;
   GamBestLat [44] :=     5.26130415787942 ;
   GamBestLat [45] :=     5.40709569515170 ;
   GamBestLat [46] :=     5.58514749724618 ;
   GamBestLat [47] :=     5.77556985268647 ;
   GamBestLat [48] :=     6.00000000000000 ;
   END InitBestLat;

(*-------------------------------------------------------------------------*)

PROCEDURE CalcLaminated ();
   (* Was used to compute the constants for the procedure InitLaminated.   *)
   (* Puts these constants in GamLaminated.                                *)
   VAR
      LambdaLamin : BVect;
      i : INTEGER;
      x : LONGREAL;
   BEGIN
   LambdaLamin[0]  :=  1.0;
   LambdaLamin[1]  :=  4.0;
   LambdaLamin[2]  :=  12.0;
   LambdaLamin[3]  :=  32.0;
   LambdaLamin[4]  :=  64.0;
   LambdaLamin[5]  :=  128.0;
   LambdaLamin[6]  :=  192.0;
   LambdaLamin[7]  :=  256.0;
   LambdaLamin[8]  :=  256.0;
   LambdaLamin[9]  :=  512.0;
   LambdaLamin[10] :=  768.0;
   LambdaLamin[11] := 1024.0;
   LambdaLamin[12] := 1024.0;
   LambdaLamin[13] := 1024.0;
   LambdaLamin[14] :=  768.0;
   LambdaLamin[15] :=  512.0;
   LambdaLamin[16] :=  256.0;
   LambdaLamin[17] :=  256.0;
   LambdaLamin[18] :=  192.0;
   LambdaLamin[19] :=  128.0;
   LambdaLamin[20] :=   64.0;
   LambdaLamin[21] :=   32.0;
   LambdaLamin[22] :=   12.0;
   LambdaLamin[23] :=    4.0;
   LambdaLamin[24] :=    1.0;
   LambdaLamin[25] :=    2.0;
   LambdaLamin[26] :=    3.0;
   LambdaLamin[27] :=    4.0;
   LambdaLamin[28] :=    4.0;
   LambdaLamin[29] :=    4.0;
   LambdaLamin[30] :=    3.0;
   LambdaLamin[31] :=    2.0;
   LambdaLamin[32] :=    1.0;
   LambdaLamin[33] :=    1.0;
   LambdaLamin[34] :=    0.75;
   LambdaLamin[35] :=    0.50;
   LambdaLamin[36] :=    0.25;
   LambdaLamin[37] :=    0.125;
   LambdaLamin[38] :=  3.0 / TwoExp [6];
   LambdaLamin[39] :=  1.0 / TwoExp [6];
   LambdaLamin[40] :=  1.0 / TwoExp [8];
   LambdaLamin[41] :=  1.0 / TwoExp [9];
   LambdaLamin[42] :=  3.0 / TwoExp [12];
   LambdaLamin[43] :=  1.0 / TwoExp [12];
   LambdaLamin[44] :=  1.0 / TwoExp [14];
   LambdaLamin[45] :=  1.0 / TwoExp [16];
   LambdaLamin[46] :=  3.0 / TwoExp [20];
   LambdaLamin[47] :=  1.0 / TwoExp [21];
   LambdaLamin[48] :=  1.0 / TwoExp [24];
   FOR i := 1 TO MaxtLaminated DO
      x := 2.0 / Pow (LambdaLamin[i], 1.0/(2.0 * IToLR(i)));
      GamLaminated[i] := x * x;
      END;
   END CalcLaminated;


PROCEDURE InitLaminated (VAR GamLaminated : BVect);
   BEGIN
   GamLaminated [ 0] :=     0.00000000000000 ;
   GamLaminated [ 1] :=     1.00000000000000 ;
   GamLaminated [ 2] :=     1.15470053837925 ;
   GamLaminated [ 3] :=     1.25992104989487 ;
   GamLaminated [ 4] :=     1.41421356237309 ;
   GamLaminated [ 5] :=     1.51571656651040 ;
   GamLaminated [ 6] :=     1.66536635531121 ;
   GamLaminated [ 7] :=     1.81144732852781 ;
   GamLaminated [ 8] :=     2.00000000000000 ;
   GamLaminated [ 9] :=     2.00000000000000 ;
   GamLaminated [10] :=     2.05837201792952 ;
   GamLaminated [11] :=     2.13008217887993 ;
   GamLaminated [12] :=     2.24492409661875 ;
   GamLaminated [13] :=     2.34692092000925 ;
   GamLaminated [14] :=     2.48864391982238 ;
   GamLaminated [15] :=     2.63901582154579 ;
   GamLaminated [16] :=     2.82842712474619 ;
   GamLaminated [17] :=     2.88668115405991 ;
   GamLaminated [18] :=     2.98682599936104 ;
   GamLaminated [19] :=     3.09851928453331 ;
   GamLaminated [20] :=     3.24900958542494 ;
   GamLaminated [21] :=     3.39145596751014 ;
   GamLaminated [22] :=     3.57278019514216 ;
   GamLaminated [23] :=     3.76602735259556 ;
   GamLaminated [24] :=     4.00000000000000 ;
   GamLaminated [25] :=     3.89061978964914 ;
   GamLaminated [26] :=     3.83450381188673 ;
   GamLaminated [27] :=     3.79980642833440 ;
   GamLaminated [28] :=     3.80678061204248 ;
   GamLaminated [29] :=     3.81328532378654 ;
   GamLaminated [30] :=     3.85616802789424 ;
   GamLaminated [31] :=     3.91155414534173 ;
   GamLaminated [32] :=     4.00000000000000 ;
   GamLaminated [33] :=     4.00000000000000 ;
   GamLaminated [34] :=     4.03398853947441 ;
   GamLaminated [35] :=     4.08000643768480 ;
   GamLaminated [36] :=     4.15703690412737 ;
   GamLaminated [37] :=     4.23124164832276 ;
   GamLaminated [38] :=     4.33546037046114 ;
   GamLaminated [39] :=     4.45012590438595 ;
   GamLaminated [40] :=     4.59479341998814 ;
   GamLaminated [41] :=     4.65735933059734 ;
   GamLaminated [42] :=     4.75016320908659 ;
   GamLaminated [43] :=     4.85364895344187 ;
   GamLaminated [44] :=     4.98703323713956 ;
   GamLaminated [45] :=     5.11791276058506 ;
   GamLaminated [46] :=     5.27922773469898 ;
   GamLaminated [47] :=     5.45208672393488 ;
   GamLaminated [48] :=     5.65685424949238 ;
   END InitLaminated;

(*-------------------------------------------------------------------------*)

PROCEDURE CalcRogers ();
   (* Was used to compute the constants for the procedure InitRogers.      *)
   (* Puts these constants in GamRogers.                                   *)
   VAR
      x : LONGREAL;
      i : INTEGER;
   BEGIN
   (* R(n) : The first 24 values are taken from table 1.5 - page 15 (1988)*)
   GamRogers[1]  := Lg (0.5);
   GamRogers[2]  := Lg (0.28868);
   GamRogers[3]  := Lg (0.1847);
   GamRogers[4]  := Lg (0.13127);
   GamRogers[5]  := Lg (0.09987);
   GamRogers[6]  := Lg (0.08112);
   GamRogers[7]  := Lg (0.06981);
   GamRogers[8]  := Lg (0.06326);
   GamRogers[9]  := Lg (0.06007);
   GamRogers[10] := Lg (0.05953);
   GamRogers[11] := Lg (0.06136);
   GamRogers[12] := Lg (0.06559);
   GamRogers[13] := Lg (0.07253);
   GamRogers[14] := Lg (0.08278);
   GamRogers[15] := Lg (0.09735);
   GamRogers[16] := Lg (0.11774);
   GamRogers[17] := Lg (0.14624);
   GamRogers[18] := Lg (0.18629);
   GamRogers[19] := Lg (0.24308);
   GamRogers[20] := Lg (0.32454);
   GamRogers[21] := Lg (0.44289);
   GamRogers[22] := Lg (0.61722);
   GamRogers[23] := Lg (0.87767);
   GamRogers[24] := Lg (1.27241);
   FOR i := 25 TO MaxtRogers DO
      GamRogers[i] :=  (0.5 * IToLR(i) * (Lg (IToLR(i) / (4.0 * e * Pi))))
  		       + (1.5 * Lg (IToLR(i))) - (Lg (e / Pow(Pi, 0.5))) 
		       + (5.25 / (IToLR(i) + 2.5));
      END;
   FOR i := 1 TO MaxtRogers DO
      x := 1.0 / Pow (2.0, ((-(GamRogers[i]/IToLR(i))) - 1.0));
      GamRogers[i] := x * x;
      END;
   END CalcRogers;


PROCEDURE InitRogers (VAR GamRogers : BVect);
   BEGIN
   GamRogers [ 0] :=     0.00000000000000 ;
   GamRogers [ 1] :=     1.00000000000000 ;
   GamRogers [ 2] :=     1.15472000000000 ;
   GamRogers [ 3] :=     1.29729254271781 ;
   GamRogers [ 4] :=     1.44924808090265 ;
   GamRogers [ 5] :=     1.59160029613060 ;
   GamRogers [ 6] :=     1.73155372907047 ;
   GamRogers [ 7] :=     1.86960880640884 ;
   GamRogers [ 8] :=     2.00605247023201 ;
   GamRogers [ 9] :=     2.14116717185029 ;
   GamRogers [10] :=     2.27513498055864 ;
   GamRogers [11] :=     2.40810550041623 ;
   GamRogers [12] :=     2.54019035763686 ;
   GamRogers [13] :=     2.67149901646505 ;
   GamRogers [14] :=     2.80206308564826 ;
   GamRogers [15] :=     2.93205054070827 ;
   GamRogers [16] :=     3.06143818820811 ;
   GamRogers [17] :=     3.19030704494659 ;
   GamRogers [18] :=     3.31871486433102 ;
   GamRogers [19] :=     3.44668834264311 ;
   GamRogers [20] :=     3.57426554375250 ;
   GamRogers [21] :=     3.70146701961630 ;
   GamRogers [22] :=     3.82832748486438 ;
   GamRogers [23] :=     3.95487056309860 ;
   GamRogers [24] :=     4.08111576477761 ;
   GamRogers [25] :=     4.20715430161030 ;
   GamRogers [26] :=     4.33285980614924 ;
   GamRogers [27] :=     4.45831966777310 ;
   GamRogers [28] :=     4.58354848402102 ;
   GamRogers [29] :=     4.70855952602871 ;
   GamRogers [30] :=     4.83336490167654 ;
   GamRogers [31] :=     4.95797569329732 ;
   GamRogers [32] :=     5.08240207475916 ;
   GamRogers [33] :=     5.20665341166885 ;
   GamRogers [34] :=     5.33073834764256 ;
   GamRogers [35] :=     5.45466487898699 ;
   GamRogers [36] :=     5.57844041967152 ;
   GamRogers [37] :=     5.70207185811435 ;
   GamRogers [38] :=     5.82556560702549 ;
   GamRogers [39] :=     5.94892764732845 ;
   GamRogers [40] :=     6.07216356700685 ;
   GamRogers [41] :=     6.19527859558027 ;
   GamRogers [42] :=     6.31827763479997 ;
   GamRogers [43] :=     6.44116528606155 ;
   GamRogers [44] :=     6.56394587495555 ;
   GamRogers [45] :=     6.68662347331408 ;
   GamRogers [46] :=     6.80920191905923 ;
   GamRogers [47] :=     6.93168483411559 ;
   GamRogers [48] :=     7.05407564061285 ;
   END InitRogers;

(*-------------------------------------------------------------------------*)

PROCEDURE CalcMinkowski ();
   (* Was used to compute the constants for the procedure InitMinkowski.   *)
   (* Puts these constants in GamMinkowski.                                *)
   VAR
      i, j, k : INTEGER;
      x, Vn, epsilon : LONGREAL;
   BEGIN

   k := 5000;
   (* Zeta de Riemann (1st 5000 terms assumed).                    *)
   (* epsilon is the error that is introduced for first k terms;   *)
   (* k is taken to be 5000.                                       *)

   FOR i := 2 TO MaxtMinkowski DO
      GamMinkowski[i] := 0.0;
      FOR j := 1 TO k DO
	 GamMinkowski[i] := GamMinkowski[i] + (1.0 
			    / Pow (IToLR(j), IToLR(i)) );
	 END;
      IF (i=1) THEN
	 epsilon := 0.0;
      ELSE
	 epsilon := 1.0 / ( ( IToLR(i) - 1.0 ) 
			   * Pow ( IToLR(k), IToLR(i) - 1.0) ); 
	 END;
      GamMinkowski[i] := GamMinkowski[i] + epsilon;
      (* 
      Vn formula from page 9 - this may have to be modified depending 
      on the support from different platforms when calculating values 
      of Vn for large values of n.
      *)
      IF NOT ODD (i) THEN
	 Vn := Pow (Pi, IToLR(i) / 2.0) / Factorielle (i DIV 2);
      ELSE
	 Vn := (TwoExp [i]) * Pow (Pi, (IToLR(i)-1.0)/2.0) * 
	       Factorielle ((i-1) DIV 2) / Factorielle (i);
	 END;
      GamMinkowski[i] := (Lg (GamMinkowski[i])) - IToLR(i) + 1.0 - (Lg (Vn));
      x := 1.0 / Pow (2.0, -(GamMinkowski[i]/IToLR(i)) - 1.0);
      GamMinkowski[i] := x * x;
      END;
   END CalcMinkowski;


PROCEDURE InitMinkowski (VAR GamMinkowski : BVect);
   BEGIN
   GamMinkowski [ 0] :=     0.00000000000000 ;
   GamMinkowski [ 1] :=     0.00000000000000 ;
   GamMinkowski [ 2] :=     1.04719756392815 ;
   GamMinkowski [ 3] :=     0.69062814882789 ;
   GamMinkowski [ 4] :=     0.66230588438641 ;
   GamMinkowski [ 5] :=     0.68895682802115 ;
   GamMinkowski [ 6] :=     0.73293650323622 ;
   GamMinkowski [ 7] :=     0.78407967437680 ;
   GamMinkowski [ 8] :=     0.83869147754813 ;
   GamMinkowski [ 9] :=     0.89517405737802 ;
   GamMinkowski [10] :=     0.95274948000853 ;
   GamMinkowski [11] :=     1.01100354118401 ;
   GamMinkowski [12] :=     1.06969923726369 ;
   GamMinkowski [13] :=     1.12869260847180 ;
   GamMinkowski [14] :=     1.18789173406828 ;
   GamMinkowski [15] :=     1.24723543612412 ;
   GamMinkowski [16] :=     1.30668158848970 ;
   GamMinkowski [17] :=     1.36620037299243 ;
   GamMinkowski [18] :=     1.42577021185918 ;
   GamMinkowski [19] :=     1.48537521407207 ;
   GamMinkowski [20] :=     1.54500351420012 ;
   GamMinkowski [21] :=     1.60464615768560 ;
   GamMinkowski [22] :=     1.66429633246555 ;
   GamMinkowski [23] :=     1.72394882699329 ;
   GamMinkowski [24] :=     1.78359964036430 ;
   GamMinkowski [25] :=     1.84324569710679 ;
   GamMinkowski [26] :=     1.90288463550686 ;
   GamMinkowski [27] :=     1.96251464853672 ;
   GamMinkowski [28] :=     2.02213436300702 ;
   GamMinkowski [29] :=     2.08174274687719 ;
   GamMinkowski [30] :=     2.14133903755970 ;
   GamMinkowski [31] :=     2.20092268604477 ;
   GamMinkowski [32] :=     2.26049331306133 ;
   GamMinkowski [33] :=     2.32005067447401 ;
   GamMinkowski [34] :=     2.37959463382297 ;
   GamMinkowski [35] :=     2.43912514042718 ;
   GamMinkowski [36] :=     2.49864221184901 ;
   GamMinkowski [37] :=     2.55814591979856 ;
   GamMinkowski [38] :=     2.61763637876553 ;
   GamMinkowski [39] :=     2.67711373682499 ;
   GamMinkowski [40] :=     2.73657816818394 ;
   GamMinkowski [41] :=     2.79602986712778 ;
   GamMinkowski [42] :=     2.85546904309690 ;
   GamMinkowski [43] :=     2.91489591667914 ;
   GamMinkowski [44] :=     2.97431071634673 ;
   GamMinkowski [45] :=     3.03371367580026 ;
   GamMinkowski [46] :=     3.09310503180911 ;
   GamMinkowski [47] :=     3.15248502245848 ;
   GamMinkowski [48] :=     3.21185388573071 ;
   END InitMinkowski;

(*-------------------------------------------------------------------------*)

PROCEDURE CalcMinkL1 ();
   (* Was used to compute the constants for the procedure InitMinkL1.      *)
   (* Puts these constants in GamMinkL1.                                   *)
   VAR
      i : INTEGER;
   BEGIN
   FOR i := 1 TO MaxtMinkL1 DO
      GamMinkL1 [i] := Lg (Factorielle (i));
      END;
   END CalcMinkL1;


PROCEDURE InitMinkL1 (VAR GamMinkL1 : BVect);
   BEGIN
   GamMinkL1 [ 0] :=     0.00000000000000 ;
   GamMinkL1 [ 1] :=     0.00000000000000 ;
   GamMinkL1 [ 2] :=     1.00000000000000 ;
   GamMinkL1 [ 3] :=     2.58496250072116 ;
   GamMinkL1 [ 4] :=     4.58496250072116 ;
   GamMinkL1 [ 5] :=     6.90689059560852 ;
   GamMinkL1 [ 6] :=     9.49185309632968 ;
   GamMinkL1 [ 7] :=    12.29920801838728 ;
   GamMinkL1 [ 8] :=    15.29920801838728 ;
   GamMinkL1 [ 9] :=    18.46913301982959 ;
   GamMinkL1 [10] :=    21.79106111471695 ;
   GamMinkL1 [11] :=    25.25049273335425 ;
   GamMinkL1 [12] :=    28.83545523407540 ;
   GamMinkL1 [13] :=    32.53589495221650 ;
   GamMinkL1 [14] :=    36.34324987427410 ;
   GamMinkL1 [15] :=    40.25014046988262 ;
   GamMinkL1 [16] :=    44.25014046988262 ;
   GamMinkL1 [17] :=    48.33760331113297 ;
   GamMinkL1 [18] :=    52.50752831257527 ;
   GamMinkL1 [19] :=    56.75545582601886 ;
   GamMinkL1 [20] :=    61.07738392090622 ;
   GamMinkL1 [21] :=    65.46970134368497 ;
   GamMinkL1 [22] :=    69.92913296232229 ;
   GamMinkL1 [23] :=    74.45269491837929 ;
   GamMinkL1 [24] :=    79.03765741910044 ;
   GamMinkL1 [25] :=    83.68151360887516 ;
   GamMinkL1 [26] :=    88.38195332701626 ;
   GamMinkL1 [27] :=    93.13684082917975 ;
   GamMinkL1 [28] :=    97.94419575123734 ;
   GamMinkL1 [29] :=   102.80217674636492 ;
   GamMinkL1 [30] :=   107.70906734197342 ;
   GamMinkL1 [31] :=   112.66326365236030 ;
   GamMinkL1 [32] :=   117.66326365236031 ;
   GamMinkL1 [33] :=   122.70765777171876 ;
   GamMinkL1 [34] :=   127.79512061296910 ;
   GamMinkL1 [35] :=   132.92440362991405 ;
   GamMinkL1 [36] :=   138.09432863135638 ;
   GamMinkL1 [37] :=   143.30378199698532 ;
   GamMinkL1 [38] :=   148.55170951042891 ;
   GamMinkL1 [39] :=   153.83711172929117 ;
   GamMinkL1 [40] :=   159.15903982417851 ;
   GamMinkL1 [41] :=   164.51659182879661 ;
   GamMinkL1 [42] :=   169.90890925157535 ;
   GamMinkL1 [43] :=   175.33517400627747 ;
   GamMinkL1 [44] :=   180.79460562491477 ;
   GamMinkL1 [45] :=   186.28645872124443 ;
   GamMinkL1 [46] :=   191.81002067730145 ;
   GamMinkL1 [47] :=   197.36460952897906 ;
   GamMinkL1 [48] :=   202.94957202970022 ;
   END InitMinkL1;

(*-------------------------------------------------------------------------*)

PROCEDURE RescaleGamma (G : Normaliz;  m : MScal;  k : MDim);
   (* Computes the vector Cst. that corresponds to G, for a lattice of     *)
   (* density m^k for t >= k, and m^t for t < k.                           *)
   VAR
      t : BDim;
      kLR, tLR, Logm, LogBeta, x, e : LONGREAL;
   BEGIN
   WITH G^ DO
      e   := 1.0;
      kLR := VAL (LONGREAL, k);
      LogBeta := Ln (Beta);
      Logm    := Ln (MScalToLR (m));
      FOR t := 1 TO Maxt DO
         tLR := VAL (LONGREAL, t);
         IF t > k THEN e := kLR / tLR END;
         x := Ln (Gamma[t]) + tLR * LogBeta + e * Logm;
         IF (Norm = L2Norm) THEN x := x + x  END;
         Cst[t] := Exp (x);
         END;       
      END
    END RescaleGamma; 

(*-------------------------------------------------------------------------*)

PROCEDURE InitNormaliz
   (   G  : Normaliz;
    Name  : ARRAY OF CHAR;
    Norm  : NormType;
    GType : GammaType;
    Beta  : LONGREAL;
    Maxt  : BDim;
       m  : MScal;
       k  : MDim
   );
   CONST
      WrongType = "InitNormaliz: GType does not match with Norm";
   BEGIN
   Assert (G <> NIL, "InitNormaliz:    Normaliz is a NIL pointer");
   Copy (G^.Name, Name);
   G^.Norm := Norm;  G^.GType := GType;  G^.Beta := Beta;   G^.Maxt := Maxt; 
   WITH G^ DO
      CASE GType OF
         BestLat   : InitBestLat (Gamma);
                     Assert (Norm = L2Norm, WrongType);
                     Assert (Maxt <= MaxtBestLat,
                        "InitBestLat: Maxt > MaxtBestLat");
       | Laminated : InitLaminated (Gamma);
                     Assert (Norm = L2Norm, WrongType);
                     Assert (Maxt <= MaxtLaminated,
                        "InitLaminated: Maxt > MaxtLaminated");
       | Minkowski : InitMinkowski (Gamma);
                     Assert (Norm = L2Norm, WrongType);
                     Assert (Maxt <= MaxtMinkowski,
                        "InitMinkowski : Maxt > MaxtMinkowski ");
       | Rogers    : InitRogers (Gamma);
                     Assert (Norm = L2Norm, WrongType);
                     Assert (Maxt <= MaxtRogers,
                        "InitRogers: Maxt > MaxtRogers");
       | MinkL1    : InitMinkL1 (Gamma);
                     Assert (Norm = L1Norm, WrongType);
                     Assert (Maxt <= MaxtMinkL1,
                        "InitMinkL1: Maxt > MaxtMinkL1");
         END;
      END;
   RescaleGamma (G, m, k);
   END InitNormaliz;

(*-------------------------------------------------------------------------*)

PROCEDURE WriteNormaliz (G : Normaliz);
   VAR
      t : BDim;
   BEGIN
   WriteString ('------------------------------');  WriteLn;
   WriteString ('Contents of Normaliz variable: '); 
   WITH G^ DO
      WriteString (Name);  WriteLn;  WriteLn;
      WriteString ('Norm = ');
      CASE Norm OF
         L1Norm  : WriteString ('L1');
       | L2Norm  : WriteString ('L2');
       | SupNorm : WriteString ('Sup');
         END;
      WriteString ('Norm');     WriteLn;
      WriteString ('Gamma type = ');
      CASE GType OF
         BestLat   : WriteString ('BestLat');
       | Laminated : WriteString ('Laminated');
       | Minkowski : WriteString ('Minkowski');
       | Rogers    : WriteString ('Rogers');
       | MinkL1    : WriteString ('MinkL1');
         END;
      WriteLn;
      WriteString ('Beta = ');   WriteLR (Beta, 6, 4, 4);   WriteLn;
      WriteLn;   WriteLn;

      WriteString ('Maxt = ');   WriteLI (Maxt, 2);   WriteLn;
      FOR t := 1 TO Maxt DO
         WriteString ("Gamma");
         WriteString (" [");
         WriteLI (t, 2);
         WriteString ("] := ");
	 WriteLR (Gamma[t], 18, 14, 14);
         WriteString (" ;");
         WriteString ("      Cst");
         WriteString (" [");
         WriteLI (t, 2);
         WriteString ("] := ");
	 WriteLR (Cst[t], 22, 12, 12);
         WriteLn;
	 END;
      END;
   WriteLn;
   END WriteNormaliz;


END NORM.
