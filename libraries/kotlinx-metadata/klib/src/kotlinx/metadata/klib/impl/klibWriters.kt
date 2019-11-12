/*
 * Copyright 2010-2019 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package kotlinx.metadata.klib.impl

import kotlinx.metadata.impl.*
import kotlinx.metadata.klib.KlibSourceFile
import org.jetbrains.kotlin.backend.common.serialization.metadata.KlibMetadataStringTable
import org.jetbrains.kotlin.metadata.ProtoBuf

class ReverseSourceFileIndexWriteExtension : WriteContextExtension {
    private val filesReverseIndex = mutableMapOf<KlibSourceFile, Int>()

    val fileIndex: List<KlibSourceFile>
        get() = filesReverseIndex
            .map { (file, index) -> index to file }
            .sortedBy { it.first }
            .map { it.second }

    fun getIndexOf(file: KlibSourceFile): Int = filesReverseIndex.getOrPut(file) {
        filesReverseIndex.size
    }
}

class KlibPackageFragmentWriter(
    stringTable: KlibMetadataStringTable,
    contextExtensions: List<WriteContextExtension> = emptyList()
) : PackageFragmentWriter(stringTable, contextExtensions) {

    fun write(): ProtoBuf.PackageFragment =
        t.build()
}