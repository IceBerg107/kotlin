/*
 * Copyright 2010-2019 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.fir.scopes.impl

import org.jetbrains.kotlin.builtins.jvm.JavaToKotlinClassMap
import org.jetbrains.kotlin.fir.FirSession
import org.jetbrains.kotlin.fir.FirSessionComponent
import org.jetbrains.kotlin.fir.declarations.FirClass
import org.jetbrains.kotlin.fir.declarations.FirRegularClass
import org.jetbrains.kotlin.fir.resolve.ScopeSession
import org.jetbrains.kotlin.fir.resolve.firSymbolProvider
import org.jetbrains.kotlin.fir.resolve.memberScopeProvider
import org.jetbrains.kotlin.fir.scopes.FirScope
import org.jetbrains.kotlin.fir.scopes.jvm.JvmMappedScope
import org.jetbrains.kotlin.name.ClassId
import org.jetbrains.kotlin.name.FqName

class FirMemberScopeProvider : FirSessionComponent {

    private val declaredMemberCache = mutableMapOf<FirClass<*>, FirScope>()
    private val nestedClassifierCache = mutableMapOf<FirClass<*>, FirNestedClassifierScope>()
    private val selfImportingCache = mutableMapOf<FqName, FirSelfImportingScope>()

    private fun wrapDeclaredScopeWithJvmMapped(
        klass: FirClass<*>,
        regularMemberScope: FirClassDeclaredMemberScope,
        scopeSession: ScopeSession
    ): FirScope {
        val javaClassId = JavaToKotlinClassMap.mapKotlinToJava(klass.symbol.classId.asSingleFqName().toUnsafe())
            ?: return regularMemberScope
        val symbolProvider = klass.session.firSymbolProvider
        val javaClass = symbolProvider.getClassLikeSymbolByFqName(javaClassId)?.fir as? FirRegularClass
            ?: return regularMemberScope
        val preparedSignatures = JvmMappedScope.prepareSignatures(javaClass)
        return if (preparedSignatures.isNotEmpty()) {
            symbolProvider.getClassUseSiteMemberScope(javaClassId, klass.session, scopeSession)?.let {
                JvmMappedScope(
                    regularMemberScope,
                    it,
                    preparedSignatures
                )
            } ?: regularMemberScope
        } else {
            regularMemberScope
        }
    }

    fun declaredMemberScope(klass: FirClass<*>, scopeSession: ScopeSession?): FirScope {
        return declaredMemberCache.getOrPut(klass) {
            val regularMemberScope = FirClassDeclaredMemberScope(klass)
            scopeSession?.let { wrapDeclaredScopeWithJvmMapped(klass, regularMemberScope, it) } ?: regularMemberScope
        }
    }

    fun nestedClassifierScope(klass: FirClass<*>): FirNestedClassifierScope {
        return nestedClassifierCache.getOrPut(klass) {
            FirNestedClassifierScope(klass)
        }
    }

    // TODO: it's better to cache this scope in ScopeSession
    fun selfImportingScope(fqName: FqName, session: FirSession): FirSelfImportingScope {
        return selfImportingCache.getOrPut(fqName) {
            FirSelfImportingScope(fqName, session)
        }
    }
}

fun declaredMemberScope(klass: FirClass<*>, scopeSession: ScopeSession? = null): FirScope {
    return klass
        .session
        .memberScopeProvider
        .declaredMemberScope(klass, scopeSession)
}

fun nestedClassifierScope(klass: FirClass<*>): FirNestedClassifierScope {
    return klass
        .session
        .memberScopeProvider
        .nestedClassifierScope(klass)
}

fun nestedClassifierScope(classId: ClassId, session: FirSession): FirLazyNestedClassifierScope {
    return FirLazyNestedClassifierScope(classId, session)
}

fun selfImportingScope(fqName: FqName, session: FirSession): FirSelfImportingScope {
    return session.memberScopeProvider.selfImportingScope(fqName, session)
}

