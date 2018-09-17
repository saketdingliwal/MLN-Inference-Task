/set_default_parameter 1 5
WITH nat(n) AS SELECT 1 UNION SELECT n+1 FROM nat SELECT TOP $parv1$ * FROM nat;