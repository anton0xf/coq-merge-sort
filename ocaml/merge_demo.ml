open Merge_sort

let () = [5;3;4;2;5;1] 
         |> merge_sort
         |> List.map string_of_int 
         |> String.concat ";" 
         |> print_string
