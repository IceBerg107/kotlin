// !JVM_DEFAULT_MODE: compatibility
// JVM_TARGET: 1.8
// WITH_RUNTIME

interface Test {
    @JvmDefault
    val test: String
        get() = "OK"

    @JvmDefault
    var test2: String
        get() = "OK"
        set(field) {}
}

// TESTED_OBJECT_KIND: function
// TESTED_OBJECTS: Test, (access\$getTest\$.+)
// FLAGS: ACC_PUBLIC, ACC_STATIC, ACC_SYNTHETIC

// TESTED_OBJECT_KIND: function
// TESTED_OBJECTS: Test, (access\$getTest2\$.+)
// FLAGS: ACC_PUBLIC, ACC_STATIC, ACC_SYNTHETIC


// TESTED_OBJECT_KIND: function
// TESTED_OBJECTS: Test, (access\$setTest2\$.+)
// FLAGS: ACC_PUBLIC, ACC_STATIC, ACC_SYNTHETIC

