CM.make "sources.cm";

let
    val testFilesFolder = "testfiles/"
    val testFileList = ["test1.tig",
                        "test2.tig",
                        "test3.tig",
                        "test4.tig",
                        "test5.tig",
                        "test6.tig",
                        "test7.tig",
                        "test8.tig",
                        "test9.tig",
                        "test10.tig",
                        "test11.tig",
                        "test12.tig",
                        "test13.tig",
                        "test14.tig",
                        "test15.tig",
                        "test16.tig",
                        "test17.tig",
                        "test18.tig",
                        "test19.tig",
                        "test2.tig",
                        "test20.tig",
                        "test21.tig",
                        "test22.tig",
                        "test23.tig",
                        "test24.tig",
                        "test25.tig",
                        "test26.tig",
                        "test27.tig",
                        "test28.tig",
                        "test29.tig"]
    val testFiles = map (fn x=>testFilesFolder^x) testFileList
in
    map (fn x=>Main.runFile x) testFiles
end

