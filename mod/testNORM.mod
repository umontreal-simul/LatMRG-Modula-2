MODULE testNORM;

FROM  NORM  IMPORT CreateGamma, WriteGamma, Normaliz, GammaType,
                   ResetGamma, DeleteGamma;

VAR
   G : Normaliz;
   tmax : INTEGER;

BEGIN
tmax := 48;
CreateGamma (G, Laminated, 1.0);
(*
WriteGamma (G, tmax);
ResetGamma (G, BestLat, 1.0);
WriteGamma (G, tmax);
ResetGamma (G, Rogers, 1.0);
WriteGamma (G, tmax);
*)
ResetGamma (G, Minkowski, 1.0);
WriteGamma (G, tmax);
DeleteGamma (G);
END testNORM.
