open Ou.Ast

let seclvl_pp = Fmt.of_to_string string_of_seclvl
let seclvl = Alcotest.testable seclvl_pp (=)

let test_le () =
  Alcotest.(check bool) "pub0 <= pub1" true @@ seclvl_le (Public K0Public) (Public K1Public);
  Alcotest.(check bool) "pvt1 <= plc1" true @@ seclvl_le (Private K1Private) (Plocal K1Plocal);
  Alcotest.(check bool) "pvt1 <= pvt2" true @@ seclvl_le (Private K1Private) (Private K2Private)

let test_join () =
  Alcotest.(check seclvl) "plc2 = pub2 /\\ plc1" (Plocal K2Plocal) (seclvl_join (Public K2Public) (Plocal K1Plocal))

let tests = [
  ("seclvl-le", `Quick, test_le);
  ("seclvl-join", `Quick, test_join)
]