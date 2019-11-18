// TARGET_BACKEND: JVM
// WITH_RUNTIME
// FILE: z.kt

object Z {
    @JvmField
    val result: String = "OK"
}

// FILE: box.kt

fun box(): String = Z.result
