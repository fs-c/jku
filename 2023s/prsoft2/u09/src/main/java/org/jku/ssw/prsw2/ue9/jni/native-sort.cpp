#include "org_jku_ssw_prsw2_ue9_jni_JNISorter.h"

namespace std {
    template<class I>
    constexpr void iter_swap(I a, I b) {
        const auto temp = *a;

        *a = *b;
        *b = temp;
    }

    template<class I>
    I min_element(I first, I last) {
        if (first == last) {
            return first;
        }

        I smallest = first++;

        for (; first != last; first++) {
            if (*first < *smallest) {
                smallest = first;
            }
        }

        return smallest;
    }
}

template<class I>
void selection_sort(I begin, I end) {
    for (auto i = begin; i != end; i++) {
        std::iter_swap(i, std::min_element(i, end));
    }
}

JNIEXPORT void JNICALL Java_org_jku_ssw_prsw2_ue9_jni_JNISorter_sort(JNIEnv *env, jclass clazz, jobjectArray arrays) {
    for (jsize row_i = 0; row_i < env->GetArrayLength(arrays); row_i++) {
        const auto row = reinterpret_cast<jintArray>(env->GetObjectArrayElement(arrays, row_i));

        jint *elements = env->GetIntArrayElements(row, nullptr);
        const auto length = env->GetArrayLength(row);

        selection_sort(elements, elements + length);

        env->ReleaseIntArrayElements(row, elements, 0);
    }
}
