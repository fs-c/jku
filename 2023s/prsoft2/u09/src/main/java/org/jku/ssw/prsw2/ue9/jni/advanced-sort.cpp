#include "org_jku_ssw_prsw2_ue9_jni_AdvancedJNISorter.h"

#include <vector>
#include <algorithm>
#include <functional>

#include <omp.h>

template<class I, class P>
void quick_sort(I first, I last, P cmp) {
    const auto N = std::distance(first, last);
	if (N <= 1)
		return;

	const auto pivot = *std::next(first, N / 2);

	const auto middle1 = std::partition(first, last, [=](auto const& elem){ 
        return cmp(elem, pivot); 
    });
	const auto middle2 = std::partition(middle1, last, [=](auto const& elem){ 
        return !cmp(pivot, elem); 
    });

    #pragma omp task shared(first, middle1, middle2, last, cmp)
	quick_sort(first, middle1, cmp);

    #pragma omp task shared(first, middle1, middle2, last, cmp)
	quick_sort(middle2, last, cmp);
}

JNIEXPORT void JNICALL Java_org_jku_ssw_prsw2_ue9_jni_AdvancedJNISorter_sort(JNIEnv *env, jclass clazz, jobjectArray arrays) {    
    #pragma omp parallel for
    for (jsize row_i = 0; row_i < env->GetArrayLength(arrays); row_i++) {
        const auto row = reinterpret_cast<jintArray>(env->GetObjectArrayElement(arrays, row_i));

        jint *elements = env->GetIntArrayElements(row, nullptr);
        const auto length = env->GetArrayLength(row);

        #pragma omp parallel
        {
            #pragma omp single
            quick_sort(elements, elements + length, std::less<>());
            #pragma omp taskwait
        }

        env->ReleaseIntArrayElements(row, elements, 0);
    }
}
