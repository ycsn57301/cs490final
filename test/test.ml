
let () =
  Alcotest.run "Ou-tests" [
    "security level", Test_seclvl.tests
  ]