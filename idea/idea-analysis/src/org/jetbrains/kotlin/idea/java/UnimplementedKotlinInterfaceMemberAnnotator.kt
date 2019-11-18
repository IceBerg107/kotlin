/*
 * Copyright 2010-2019 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.idea.java

import com.intellij.codeInsight.ClassUtil.getAnyMethodToImplement
import com.intellij.codeInsight.daemon.JavaErrorMessages
import com.intellij.codeInsight.daemon.impl.analysis.HighlightNamesUtil.getClassDeclarationTextRange
import com.intellij.codeInsight.daemon.impl.analysis.HighlightUtil
import com.intellij.codeInsight.daemon.impl.analysis.JavaHighlightUtil
import com.intellij.codeInsight.intention.QuickFixFactory
import com.intellij.lang.annotation.Annotation
import com.intellij.lang.annotation.AnnotationHolder
import com.intellij.lang.annotation.Annotator
import com.intellij.psi.*
import com.intellij.psi.stubs.StubTreeLoader
import com.jetbrains.rd.util.currentThreadName
import org.jetbrains.kotlin.asJava.builder.toLightClassOrigin
import org.jetbrains.kotlin.asJava.classes.KtLightClassForSourceDeclaration
import org.jetbrains.kotlin.asJava.elements.KtLightMethod
import org.jetbrains.kotlin.asJava.elements.KtLightMethodImpl
import org.jetbrains.kotlin.idea.KotlinLanguage
import org.jetbrains.kotlin.idea.caches.lightClasses.KtLightClassForDecompiledDeclaration
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.name.Name
import org.jetbrains.kotlin.psi.KtUserType
import org.jetbrains.kotlin.resolve.annotations.JVM_STATIC_ANNOTATION_FQ_NAME
import org.jetbrains.kotlin.resolve.jvm.annotations.JVM_DEFAULT_FQ_NAME
import org.jetbrains.kotlin.utils.ifEmpty

class UnimplementedKotlinInterfaceMemberAnnotator : Annotator {
    override fun annotate(element: PsiElement, holder: AnnotationHolder) {
        if (element !is PsiClass || element.language == KotlinLanguage.INSTANCE) return

        if (element.isInterface || element.hasModifierProperty(PsiModifier.ABSTRACT)) return

        if (getAnyMethodToImplement(element) != null) return // reported by java default annotator

        findUnimplementedMethod(element)?.let {
            report(it, holder, element)
        }

    }

    private fun PsiMethod.getAnnotationsForCompiledDeclaration(): Sequence<String> {
        if (this !is KtLightMethodImpl) return emptySequence()
        if (this.containingClass !is KtLightClassForDecompiledDeclaration) return emptySequence()
        val origin = kotlinOrigin ?: return emptySequence()

        fun KtUserType.toFqName(): String? {
            var result: String = referencedName ?: return null
            var currentQualifier = qualifier
            while (currentQualifier !== null) {
                currentQualifier.referencedName ?: return null
                result = "${currentQualifier.referencedName}.$result"
                currentQualifier = currentQualifier.qualifier
            }
            return result
        }

        return origin.annotationEntries
            .asSequence()
            .map { (it.typeReference?.typeElement as? KtUserType)?.toFqName() }
            .filterNotNull()
    }

    private fun findUnimplementedMethod(psiClass: PsiClass): KtLightMethod? {
        val signaturesFromKotlinInterfaces = psiClass.visibleSignatures.filter { signature ->
            signature.method.let { it is KtLightMethod && it.hasModifierProperty(PsiModifier.DEFAULT) }
        }.ifEmpty { return null }

        val kotlinSuperClass = generateSequence(psiClass) { it.superClass }.firstOrNull { it is KtLightClassForSourceDeclaration }

        val signaturesVisibleThroughKotlinSuperClass = kotlinSuperClass?.visibleSignatures ?: emptyList()
        return signaturesFromKotlinInterfaces.firstOrNull {
            it !in signaturesVisibleThroughKotlinSuperClass &&
                    it.method.modifierList.annotations.none { annotation ->
                        val qualifiedName = annotation.qualifiedName
                        qualifiedName == JVM_DEFAULT_FQ_NAME.asString() || qualifiedName == JVM_STATIC_ANNOTATION_FQ_NAME.asString()
                    } &&
                    it.method.getAnnotationsForCompiledDeclaration().none { qualifiedName ->
                        qualifiedName == JVM_DEFAULT_FQ_NAME.asString() || qualifiedName == JVM_STATIC_ANNOTATION_FQ_NAME.asString()
                    }
        }?.method as? KtLightMethod
    }

    private fun report(method: KtLightMethod, holder: AnnotationHolder, psiClass: PsiClass) {
        val key = if (psiClass is PsiEnumConstantInitializer) "enum.constant.should.implement.method" else "class.must.be.abstract"
        val message = JavaErrorMessages.message(
            key, HighlightUtil.formatClass(psiClass, false), JavaHighlightUtil.formatMethod(method),
            HighlightUtil.formatClass(method.containingClass, false)
        )
        val errorAnnotation = holder.createErrorAnnotation(getClassDeclarationTextRange(psiClass), message)
        registerFixes(errorAnnotation, psiClass)
    }

    private fun registerFixes(errorAnnotation: Annotation, psiClass: PsiClass) {
        val quickFixFactory = QuickFixFactory.getInstance()
        // this code is untested
        // see com.intellij.codeInsight.daemon.impl.analysis.HighlightClassUtil.checkClassWithAbstractMethods
        errorAnnotation.registerFix(quickFixFactory.createImplementMethodsFix(psiClass))
        if (psiClass !is PsiAnonymousClass && psiClass.modifierList?.hasExplicitModifier(PsiModifier.FINAL) != true) {
            errorAnnotation.registerFix(quickFixFactory.createModifierListFix(psiClass, PsiModifier.ABSTRACT, true, false))
        }
    }
}