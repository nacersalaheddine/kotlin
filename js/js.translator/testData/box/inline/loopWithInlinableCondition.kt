// EXPECTED_REACHABLE_NODES: 1122
// IGNORE_BACKEND: JS_IR
/*
Modified test case from issue: https://youtrack.jetbrains.com/issue/KT-24542
 */
package foo

class Test(var output: String = "") {
    inline fun foo(): Boolean {
        output += "4"
        return false
    }

    fun run(doBreak: Boolean, doContinue: Boolean) {
        do {
            output += "1"
            if (doBreak) break
            output += "2"
            if (doContinue) continue
            output += "3"
        }
        while(foo())
    }
}

fun test(doBreak: Boolean, doContinue: Boolean): String {
    var x = Test()
    x.run(doBreak, doContinue)
    return x.output
}

fun box(): String {
    val test1 = test(true, true)
    val test2 = test(true, false)
    val test3 = test(false, true)
    val test4 = test(false, false)

    if (test1 != "1") return "Test1 output: ${test1}"
    if (test2 != "1") return "Test2 output: ${test2}"
    if (test3 != "124") return "Test3 output: ${test3}"
    if (test4 != "1234") return "Test4 output: ${test4}"

    return "OK"
}