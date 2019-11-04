/*
 * Copyright 2010-2019 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.idea.core.script.configuration.cache

import com.intellij.openapi.project.Project
import com.intellij.openapi.vfs.VirtualFile
import org.jetbrains.kotlin.psi.KtFile
import org.jetbrains.kotlin.scripting.resolve.ScriptCompilationConfigurationWrapper
import kotlin.script.experimental.api.ScriptDiagnostic

interface CachedConfigurationInputs {
    fun isUpToDate(project: Project, file: VirtualFile, ktFile: KtFile? = null): Boolean

    object OutOfDate : CachedConfigurationInputs {
        override fun isUpToDate(project: Project, file: VirtualFile, ktFile: KtFile?): Boolean = false
    }

    data class PsiModificationStamp(val modificationStamp: Long) : CachedConfigurationInputs {
        override fun isUpToDate(project: Project, file: VirtualFile, ktFile: KtFile?): Boolean =
            ktFile?.modificationStamp == modificationStamp
    }
}

data class ScriptConfigurationSnapshot(
    val inputs: CachedConfigurationInputs,
    val reports: List<ScriptDiagnostic>,
    val configuration: ScriptCompilationConfigurationWrapper?
)

data class ScriptConfigurationState(
    val applied: ScriptConfigurationSnapshot? = null,
    val loaded: ScriptConfigurationSnapshot? = null
) {
    fun isUpToDate(project: Project, file: VirtualFile, ktFile: KtFile? = null): Boolean =
        (loaded ?: applied)?.inputs?.isUpToDate(project, file, ktFile) ?: false
}

/**
 * Cached configurations for file's specific snapshot state.
 *
 * Writer should put related inputs snapshot for loaded configuration.
 * Reader may do up-to-date check for existed entry.
 */
interface ScriptConfigurationCache {
    operator fun get(file: VirtualFile): ScriptConfigurationState?

    fun setApplied(file: VirtualFile, configurationSnapshot: ScriptConfigurationSnapshot)
    fun setLoaded(file: VirtualFile, configurationSnapshot: ScriptConfigurationSnapshot)
    fun markOutOfDate(file: VirtualFile)

    fun allApplied(): Collection<Pair<VirtualFile, ScriptCompilationConfigurationWrapper>>
}