        // =========================================================
        // 1. DATA & STATE ARCHITECTURE
        // =========================================================
        
        const fallbackCore = { "GRE-Remaining": {}, "GRE-Frequent": {}, "GRE-Selected": {}, "GRE-Extra": {} };
        const vocabularyDB = typeof coreDatabase !== 'undefined' ? coreDatabase : fallbackCore;

        // Stable, flattened list of every word in the database, built once at
        // load time (same object references as vocabularyDB, not copies). This
        // lets us save/sync a word as a single number instead of duplicating its
        // full word/type/def/example text in localStorage and the cloud save.
        const flatWordList = [];
        const wordIndexMap = new Map(); // "word\u0000def" -> index in flatWordList
        Object.keys(vocabularyDB).forEach(cat => {
            Object.keys(vocabularyDB[cat]).forEach(set => {
                vocabularyDB[cat][set].forEach(w => {
                    const key = w.word + '\u0000' + w.def;
                    if (!wordIndexMap.has(key)) wordIndexMap.set(key, flatWordList.length);
                    flatWordList.push(w);
                });
            });
        });

        // Resolves a word object - whether it's a direct database reference or a
        // shallow copy of one (e.g. the {..., _idx} objects used by the matching
        // game) - back to its stable index in flatWordList.
        function getWordIndex(wordObj) {
            if (!wordObj || !wordObj.word) return -1;
            const key = wordObj.word + '\u0000' + wordObj.def;
            if (wordIndexMap.has(key)) return wordIndexMap.get(key);
            // Fallback: match by word text alone (covers hand-edited data or a
            // def that no longer matches exactly) so the reference isn't lost.
            for (let i = 0; i < flatWordList.length; i++) {
                if (flatWordList[i].word === wordObj.word) return i;
            }
            return -1;
        }

        function getWordByIndex(idx) {
            return (typeof idx === 'number' && idx >= 0 && idx < flatWordList.length) ? flatWordList[idx] : null;
        }

        // One-time migration: older saves (local or pulled from the cloud) stored
        // the full word object for each missed/last-seen word. Convert those into
        // indexes the first time they're encountered so existing progress isn't
        // lost when this version loads. Mutates the object/array in place and
        // returns whether anything changed.
        function migrateMissedWordsToIndexes(db) {
            let changed = false;
            Object.keys(db).forEach(key => {
                const val = db[key];
                if (val && typeof val === 'object') {
                    db[key] = getWordIndex(val);
                    changed = true;
                }
            });
            return changed;
        }

        function migrateLastSeenToIndexes(list) {
            let changed = false;
            const migrated = list.map(entry => {
                if (entry && typeof entry === 'object' && typeof entry.idx !== 'number') {
                    changed = true;
                    return { idx: getWordIndex(entry), isCorrect: entry.isCorrect };
                }
                return entry;
            });
            return { migrated, changed };
        }

        // Reads a JSON value from localStorage without ever throwing. If the stored
        // value is corrupted (manual edit, interrupted write, browser bug, etc.),
        // a raw JSON.parse would throw synchronously and, at top-level, would stop
        // the rest of this script from running at all. Instead we log it, remove
        // the bad key so it doesn't keep failing on every future load, and fall
        // back to a safe default.
        function safeLocalStorageGetJSON(key, fallback) {
            let raw = null;
            try {
                raw = localStorage.getItem(key);
            } catch (err) {
                console.error(`Could not read localStorage key "${key}":`, err);
                return fallback;
            }
            if (!raw) return fallback;
            try {
                return JSON.parse(raw);
            } catch (err) {
                console.error(`Corrupted data in localStorage key "${key}", resetting to default:`, err);
                try { localStorage.removeItem(key); } catch (e) {}
                return fallback;
            }
        }

        // Escapes regex metacharacters in a word before it's dropped into a
        // dynamically-built RegExp (used to bold the word inside example
        // sentences). Words can contain characters like "-", "'", "(", ")", "."
        // etc.; without escaping, some of those can throw a SyntaxError or match
        // incorrectly when used unescaped in a pattern.
        function escapeRegExp(str) {
            return str.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
        }

        let appData = [];
        let currentIndex = 0;
        let mode = 'mcq';
        let isFlipped = false;
        let isAnswered = false;
        let isReviewMode = false;
        let isSessionComplete = false;
        let sessionEndTimeout = null;
        let isCardCollapsed = false;
        let hasAutoPronouncedThisCard = false;
        
        let missedWordsDB = safeLocalStorageGetJSON('greMissedWords', {});
        if (migrateMissedWordsToIndexes(missedWordsDB)) {
            localStorage.setItem('greMissedWords', JSON.stringify(missedWordsDB));
        }
        (function migrateLastSeenStorage() {
            const list = safeLocalStorageGetJSON('greLastSeenWords', []);
            const { migrated, changed } = migrateLastSeenToIndexes(list);
            if (changed) localStorage.setItem('greLastSeenWords', JSON.stringify(migrated));
        })();
        let progressDB = safeLocalStorageGetJSON('greProgressDB', {});
        let hasUnsavedChanges = false;

        // Swipe & Toss state variables
        let preventNextFlip = false;
        let startX = 0;
        let startY = 0;
        let startTime = 0;
        let isDraggingCard = false;
        const dragThreshold = 15; // Increased to 15 to make quick tapping more forgiving
        const tossThreshold = 140; // Reduced to 140px to make swiping easier
        const rotationFactor = 0.18;
        const maxGlowDistance = 300;
        let justTossed = false;

        // Drag Match state variables
        let sessionMatchedIndices = new Set();
        let currentMatchingWords = [];
        let matchedCount = 0;
        let matchingMistakes = new Set();
        let selectedWordEl = null; // for tap-to-match fallback
        let successLiftTimeout = null;
        let activeDragPointerId = null;
        let activeDragEl = null;
        let activeDragWordObj = null;
        let initialX = 0;
        let initialY = 0;

        // Fill in the Blanks shuffled order
        let fillBlanksOrder = null; // shuffled index array, or null if not fill-blanks
        let fillBlanksPointer = 0; // pointer into fillBlanksOrder
        let reviewTossPending = false;
        let reviewCorrectCount = 0;

        // =========================================================
        // 2. THEME & UI TOGGLES
        // =========================================================
        function initThemeIcon() {
            const isDark = document.documentElement.classList.contains('dark');
            const icon = document.getElementById('theme-icon');
            if(isDark) {
                icon.innerHTML = `<path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 3v1m0 16v1m9-9h-1M4 12H3m15.364 6.364l-.707-.707M6.343 6.343l-.707-.707m12.728 0l-.707.707M6.343 17.657l-.707.707M16 12a4 4 0 11-8 0 4 4 0 018 0z"></path>`; 
            } else {
                icon.innerHTML = `<path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M20.354 15.354A9 9 0 018.646 3.646 9.003 9.003 0 0012 21a9.003 9.003 0 008.354-5.646z"></path>`; 
            }
        }

        function toggleDarkMode() {
            const isDark = document.documentElement.classList.toggle('dark');
            localStorage.setItem('greDarkMode', isDark ? 'dark' : 'light');
            initThemeIcon();
        }

        let _navStack = ['setup-screen'];

        function _hideAllContentScreens() {
            // Reset PC-only scroll locks
            const mainEl = document.querySelector('main');
            if (mainEl) {
                mainEl.classList.remove('md:overflow-hidden');
            }
            document.body.classList.remove('md:overflow-hidden');

            ['setup-screen','dashboard-screen','settings-screen','study-screen','library-screen','passage-screen'].forEach(id => {
                const el = document.getElementById(id);
                if (!el) return;
                if (id === 'study-screen' || id === 'library-screen' || id === 'passage-screen') {
                    el.classList.add('hidden');
                    el.classList.remove('flex');
                } else {
                    el.classList.add('hidden');
                }
            });
            document.getElementById('game-header').classList.add('hidden');
            document.getElementById('game-header').classList.remove('flex');
            document.getElementById('next-btn-container').classList.add('hidden');
        }

        function _showScreen(id) {
            _hideAllContentScreens();
            const brandTitle = document.getElementById('nav-brand-title');
            if (brandTitle) {
                if (id === 'passage-screen') {
                    brandTitle.innerText = "GRE Verbal Reasoning";
                } else {
                    brandTitle.innerText = "GRE Vocab";
                }
            }

            if (id === 'setup-screen') {
                document.getElementById('setup-screen').classList.remove('hidden');
                document.getElementById('end-session-btn').classList.add('hidden');
                document.getElementById('nav-branding').classList.remove('hidden');
                document.querySelector('main').style.paddingTop = 'max(1.25rem, 2.5vh)';
                document.body.classList.remove('overflow-hidden');
                document.body.style.touchAction = '';
                updateMissedUI();
                updateSetOptions();
            } else if (id === 'study-screen') {
                document.getElementById('study-screen').classList.remove('hidden');
                document.getElementById('study-screen').classList.add('flex');
                document.getElementById('end-session-btn').classList.remove('hidden');
                document.getElementById('nav-branding').classList.add('hidden');
                document.querySelector('main').style.paddingTop = '0.5rem';
                document.body.classList.add('overflow-hidden');
                document.body.style.touchAction = 'none';
            } else if (id === 'library-screen') {
                document.getElementById('library-screen').classList.remove('hidden');
                document.getElementById('library-screen').classList.add('flex');
                document.getElementById('end-session-btn').classList.add('hidden');
                document.getElementById('nav-branding').classList.remove('hidden');
                document.querySelector('main').style.paddingTop = 'max(1.25rem, 2.5vh)';
                document.body.classList.remove('overflow-hidden');
                document.body.style.touchAction = '';
            } else if (id === 'passage-screen') {
                document.getElementById('passage-screen').classList.remove('hidden');
                document.getElementById('passage-screen').classList.add('flex');
                document.getElementById('end-session-btn').classList.add('hidden');
                document.getElementById('nav-branding').classList.remove('hidden');
                document.querySelector('main').style.paddingTop = 'max(1.25rem, 2.5vh)';
                
                // Lock body/main scrolling on PC only
                const mainEl = document.querySelector('main');
                if (mainEl) {
                    mainEl.classList.add('md:overflow-hidden');
                }
                document.body.classList.add('md:overflow-hidden');
                
                document.body.style.touchAction = '';
            } else {
                document.getElementById(id).classList.remove('hidden');
                document.getElementById('end-session-btn').classList.add('hidden');
                document.getElementById('nav-branding').classList.remove('hidden');
            }
        }

        function showSetup() {
            _navStack = ['setup-screen'];
            _showScreen('setup-screen');
        }

        function goToMainFromNav() {
            if (_navStack.includes('study-screen') && !confirm('Leave your current study session and return to main menu? Progress will be saved.')) {
                return;
            }
            _navStack = ['setup-screen'];
            const setupScreen = document.getElementById('setup-screen');
            setupScreen.classList.remove('fade-in');
            _showScreen('setup-screen');
            requestAnimationFrame(() => {
                setupScreen.classList.add('fade-in');
            });
        }

        function _goBack() {
            _navStack.pop();
            _showScreen(_navStack[_navStack.length - 1] || 'setup-screen');
        }

        function toggleMoreNavMenu() {
            const menu = document.getElementById('nav-more-menu');
            const btn = document.getElementById('more-nav-btn');
            const isOpen = menu.classList.contains('expanded');
            
            if (!isOpen) {
                menu.classList.add('expanded');
                btn.querySelector('svg').classList.add('rotate-90');
            } else {
                menu.classList.remove('expanded');
                btn.querySelector('svg').classList.remove('rotate-90');
            }
            haptic();
        }

        function goToMemoryPalace() {
            if (_navStack.includes('study-screen') && !confirm('Leave your current study session and go to Memory Palace? Progress will be saved.')) {
                return;
            }
            window.location.href = 'memory_palace.html';
        }

        function goToVocabGroups() {
            if (_navStack.includes('study-screen') && !confirm('Leave your current study session and go to Vocab Groups? Progress will be saved.')) {
                return;
            }
            window.location.href = 'vocab_groups.html';
        }

        // =========================================================
        // LIBRARY MODULE
        // =========================================================
        let libraryState = {
            view: 'tomes', // 'tomes', 'books', 'words'
            category: null,
            set: null,
            sort: 'az'
        };

        function getFriendlyModeName(rawMode) {
            if (rawMode === 'mcq') return 'Quiz';
            if (rawMode === 'flashcard') return 'Flashcard';
            if (rawMode === 'matching') return 'Match';
            if (rawMode === 'fillblanks') return 'Fill in the Blanks';
            return rawMode;
        }

        function recordWordGameStatus(word, status) {
            if (!word) return;
            const cleanWord = word.trim().toLowerCase();
            const friendlyMode = getFriendlyModeName(mode);
            
            const wordStatuses = safeLocalStorageGetJSON('greWordStatuses', {});
            wordStatuses[cleanWord] = {
                status: status,
                mode: friendlyMode,
                timestamp: Date.now()
            };
            
            localStorage.setItem('greWordStatuses', JSON.stringify(wordStatuses));
            hasUnsavedChanges = true;

            if (status === 'mastered' && localStorage.getItem('greSyncMasteredToLearned') === 'true') {
                const learnedList = safeLocalStorageGetJSON('learned-words', []);
                const learnedSet = new Set(learnedList.map(w => w.trim().toLowerCase()));
                if (!learnedSet.has(cleanWord)) {
                    learnedSet.add(cleanWord);
                    localStorage.setItem('learned-words', JSON.stringify(Array.from(learnedSet)));
                }
            }
        }

        function goToLibrary() {
            if (_navStack.includes('study-screen') && !confirm('Leave your current study session and open the Library? Progress will be saved.')) {
                return;
            }
            _navStack = ['setup-screen', 'library-screen'];
            _showScreen('library-screen');
            showLibraryTomes();
        }

        function libraryBack() {
            if (libraryState.view === 'words') {
                selectLibraryCategory(libraryState.category);
            } else if (libraryState.view === 'books') {
                showLibraryTomes();
            } else {
                _navStack.pop();
                _showScreen('setup-screen');
            }
        }

        function showLibraryTomes() {
            libraryState.view = 'tomes';
            libraryState.category = null;
            libraryState.set = null;

            document.getElementById('library-title').innerText = "Library";
            document.getElementById('library-subtitle').innerText = "Choose a category to browse";

            renderLibrarySubActions();

            const container = document.getElementById('library-content');
            container.scrollTop = 0;
            const mainEl = document.querySelector('main');
            if (mainEl) mainEl.scrollTop = 0;

            const categories = Object.keys(vocabularyDB).filter(cat => Object.keys(vocabularyDB[cat]).length > 0);

            if (categories.length === 0) {
                container.innerHTML = `<div class="text-center py-12 text-slate-400 dark:text-slate-500 font-medium">No categories found. Load database.js first.</div>`;
                return;
            }

            // Read learned words
            const learnedList = safeLocalStorageGetJSON('learned-words', []);
            const learnedSet = new Set(learnedList.map(w => w.trim().toLowerCase()));

            // Generate category cards
            const gridHTML = `
                <div class="grid grid-cols-1 sm:grid-cols-2 gap-4 p-2">
                    ${categories.map((cat, idx) => {
                        // Count sets and total words
                        const sets = Object.keys(vocabularyDB[cat]);
                        let wordCount = 0;
                        let completedBooks = 0;
                        
                        sets.forEach(s => {
                            const setWords = vocabularyDB[cat][s];
                            const totalWords = setWords.length;
                            const learnedCount = setWords.filter(w => learnedSet.has(w.word.trim().toLowerCase())).length;
                            if (totalWords > 0 && learnedCount === totalWords) {
                                completedBooks++;
                            }
                            wordCount += totalWords;
                        });

                        const completionText = completedBooks > 0
                            ? ` • <span class="text-emerald-600 dark:text-emerald-400 font-semibold">${completedBooks} completed</span>`
                            : '';

                        return `
                            <div onclick="selectLibraryCategory('${cat}')" class="tome-card rounded-2xl p-6 cursor-pointer flex flex-col justify-between min-h-[140px] shadow-sm relative overflow-hidden group">
                                <div class="relative z-10">
                                    <h3 class="text-lg sm:text-xl font-bold font-serif text-slate-800 dark:text-white mb-1 group-hover:text-primary-600 dark:group-hover:text-primary-400 transition-colors">${cat}</h3>
                                    <p class="text-xs sm:text-sm text-slate-500 dark:text-slate-400 font-medium">${sets.length} Books${completionText}</p>
                                </div>
                                <div class="flex justify-between items-end mt-4 relative z-10">
                                    <span class="text-xs font-semibold px-2.5 py-1 bg-white/60 dark:bg-neutral-800/80 backdrop-blur-sm border border-slate-200/50 dark:border-neutral-700/50 rounded-full text-slate-600 dark:text-slate-300">${wordCount} Words</span>
                                    <span class="text-primary-600 dark:text-primary-400 text-sm font-semibold inline-flex items-center gap-1 opacity-0 group-hover:opacity-100 transition-opacity">
                                        Browse
                                        <svg class="w-4 h-4 transform group-hover:translate-x-1 transition-transform" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 5l7 7-7 7"></path></svg>
                                    </span>
                                </div>
                                <!-- Background watermark icon -->
                                <svg class="absolute -right-4 -bottom-4 w-24 h-24 text-slate-200/40 dark:text-neutral-800/20 transform -rotate-12 pointer-events-none transition-transform group-hover:scale-110" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                                    <path stroke-linecap="round" stroke-linejoin="round" stroke-width="1.5" d="M12 6.253v13m0-13C10.832 5.477 9.246 5 7.5 5S4.168 5.477 3 6.253v13C4.168 18.477 5.754 18 7.5 18s3.332.477 4.5 1.253m0-13C13.168 5.477 14.754 5 16.5 5c1.747 0 3.332.477 4.5 1.253v13C19.832 18.477 18.247 18 16.5 18c-1.746 0-3.332.477-4.5 1.253"></path>
                                </svg>
                            </div>
                        `;
                    }).join('')}
                </div>
            `;
            container.innerHTML = gridHTML;
        }

        function selectLibraryCategory(cat) {
            libraryState.view = 'books';
            libraryState.category = cat;
            libraryState.set = null;

            document.getElementById('library-title').innerText = cat;
            document.getElementById('library-subtitle').innerText = "Choose a book to read";

            const actionsContainer = document.getElementById('library-sub-actions');
            if (actionsContainer) {
                actionsContainer.innerHTML = '';
            }

            const container = document.getElementById('library-content');
            container.scrollTop = 0;
            const mainEl = document.querySelector('main');
            if (mainEl) mainEl.scrollTop = 0;

            const sets = Object.keys(vocabularyDB[cat] || {});

            if (sets.length === 0) {
                container.innerHTML = `<div class="text-center py-12 text-slate-400 dark:text-slate-500 font-medium">No books found in this category.</div>`;
                return;
            }

            // Read learned words
            const learnedList = safeLocalStorageGetJSON('learned-words', []);
            const learnedSet = new Set(learnedList.map(w => w.trim().toLowerCase()));

            // Build detailed book items
            const bookDetailsList = sets.map(s => {
                const setWords = [...vocabularyDB[cat][s]];
                const totalWords = setWords.length;
                const learnedCount = setWords.filter(w => learnedSet.has(w.word.trim().toLowerCase())).length;
                const ratio = totalWords > 0 ? (learnedCount / totalWords) : 0;
                return {
                    name: s,
                    words: setWords,
                    totalWords,
                    learnedCount,
                    ratio
                };
            });

            // Sort by progress descending. If equal, sort numerically (Set 1 before Set 2)
            bookDetailsList.sort((a, b) => {
                if (b.ratio !== a.ratio) {
                    return b.ratio - a.ratio; // progress descending
                }
                return a.name.localeCompare(b.name, undefined, {numeric: true, sensitivity: 'base'});
            });

            // Render shelves of books
            // We group books into rows of 4 for beautiful visual presentation
            const booksPerRow = 4;
            let shelfHTML = `<div class="flex flex-col gap-2 p-2">`;

            for (let i = 0; i < bookDetailsList.length; i += booksPerRow) {
                const rowDetails = bookDetailsList.slice(i, i + booksPerRow);
                shelfHTML += `
                    <div class="library-shelf-container">
                        ${rowDetails.map((book, idx) => {
                            const s = book.name;
                            const setWords = [...book.words].sort((a, b) => a.word.localeCompare(b.word));
                            const totalWords = book.totalWords;
                            const learnedCount = book.learnedCount;
                            const isFullyLearned = (totalWords > 0 && learnedCount === totalWords);
                            const fullyLearnedClass = isFullyLearned ? " fully-learned" : "";

                            const firstWord = setWords[0] ? setWords[0].word : '';
                            const lastWord = setWords[setWords.length - 1] ? setWords[setWords.length - 1].word : '';
                            
                            // Format according to word casing settings
                            const displayFirst = formatWordBySetting(firstWord);
                            const displayLast = formatWordBySetting(lastWord);

                            // Generate a distinct book cover color based on category and set index
                            const bookColors = [
                                'from-[#881337] to-[#4c0519] border-rose-950', // deep crimson
                                'from-[#064e3b] to-[#022c22] border-emerald-950', // emerald green
                                'from-[#1e3a8a] to-[#172554] border-blue-950', // navy blue
                                'from-[#701a75] to-[#4a044e] border-fuchsia-950', // deep purple
                                'from-[#7c2d12] to-[#451a03] border-orange-950', // warm brown
                                'from-[#115e59] to-[#134e4a] border-teal-950'  // teal
                            ];
                            const coverColor = bookColors[(i + idx) % bookColors.length];

                            return `
                                <div class="book-container">
                                    <div onclick="openLibraryBook('${s}')" class="book-cover bg-gradient-to-br ${coverColor} border-t border-r border-b${fullyLearnedClass}">
                                        <div class="book-spine-label">${cat}</div>
                                        <div class="book-title-container">
                                            <div class="book-title">${s}</div>
                                            <div class="text-[9px] sm:text-[10px] opacity-80 mt-1 font-sans">Learned ${learnedCount}/${totalWords} words</div>
                                        </div>
                                        <div class="book-range">${displayFirst}<br/><span class="opacity-50 text-[10px]">to</span><br/>${displayLast}</div>
                                    </div>
                                </div>
                            `;
                        }).join('')}
                    </div>
                    <div class="shelf-wood"></div>
                `;
            }
            shelfHTML += `</div>`;
            container.innerHTML = shelfHTML;
        }

        function openLibraryBook(set) {
            libraryState.view = 'words';
            libraryState.set = set;

            const cat = libraryState.category;
            document.getElementById('library-title').innerText = `${cat} / ${set}`;
            document.getElementById('library-subtitle').innerText = "Double tap to mark learned";

            const actionsContainer = document.getElementById('library-sub-actions');
            if (actionsContainer) {
                actionsContainer.innerHTML = '';
            }

            const container = document.getElementById('library-content');
            container.scrollTop = 0;
            const mainEl = document.querySelector('main');
            if (mainEl) mainEl.scrollTop = 0;

            const sortedWords = [...vocabularyDB[cat][set]].sort((a, b) => a.word.localeCompare(b.word));

            if (sortedWords.length === 0) {
                container.innerHTML = `<div class="text-center py-12 text-slate-400 dark:text-slate-500 font-medium">No words found in this book.</div>`;
                return;
            }

            const learnedList = safeLocalStorageGetJSON('learned-words', []);
            const learnedSet = new Set(learnedList.map(w => w.trim().toLowerCase()));
            const wordStatuses = safeLocalStorageGetJSON('greWordStatuses', {});

            // Generate Word List
            const listHTML = `
                <div class="space-y-4 p-2 pb-12">
                    <div class="flex flex-col gap-3 bg-slate-50 dark:bg-neutral-800/40 px-2.5 sm:px-3.5 py-3 rounded-xl border border-slate-200/50 dark:border-neutral-800/50 mb-4 shrink-0">
                        <div class="flex justify-between items-center">
                            <span class="text-xs sm:text-sm font-semibold text-slate-600 dark:text-slate-300" id="library-word-count">${sortedWords.length} Words in Book</span>
                            <button onclick="toggleAllLibraryExamples(this)" class="px-3 py-1.5 bg-primary-600 text-white hover:bg-primary-700 rounded-lg text-xs font-semibold shadow-sm transition-colors focus:outline-none">
                                Expand All Examples
                            </button>
                        </div>
                        <div class="flex items-center gap-x-2.5 sm:gap-x-4 gap-y-2 text-xs font-semibold text-slate-500 dark:text-slate-400 border-t border-slate-200/50 dark:border-neutral-800/50 pt-2.5 mt-1 select-none flex-wrap">
                            <label class="inline-flex items-center gap-1.5 cursor-pointer hover:text-slate-800 dark:hover:text-neutral-200 transition-colors">
                                <input type="radio" name="lib-filter" value="all" checked onchange="filterLibraryWords(this.value)" class="w-3.5 h-3.5 accent-primary-600 dark:accent-primary-400 cursor-pointer">
                                <span>All</span>
                            </label>
                            <label class="inline-flex items-center gap-1.5 cursor-pointer hover:text-slate-800 dark:hover:text-neutral-200 transition-colors">
                                <input type="radio" name="lib-filter" value="mastered" onchange="filterLibraryWords(this.value)" class="w-3.5 h-3.5 accent-primary-600 dark:accent-primary-400 cursor-pointer">
                                <span>Mastered</span>
                            </label>
                            <label class="inline-flex items-center gap-1.5 cursor-pointer hover:text-slate-800 dark:hover:text-neutral-200 transition-colors">
                                <input type="radio" name="lib-filter" value="review" onchange="filterLibraryWords(this.value)" class="w-3.5 h-3.5 accent-primary-600 dark:accent-primary-400 cursor-pointer">
                                <span>In Review</span>
                            </label>
                            <label class="inline-flex items-center gap-1.5 cursor-pointer hover:text-slate-800 dark:hover:text-neutral-200 transition-colors">
                                <input type="radio" name="lib-filter" value="notseen" onchange="filterLibraryWords(this.value)" class="w-3.5 h-3.5 accent-primary-600 dark:accent-primary-400 cursor-pointer">
                                <span>Not Seen</span>
                            </label>
                        </div>
                    </div>
                    ${sortedWords.map((w, idx) => {
                        const wordId = `lib-word-ex-${idx}`;
                        // We will check if both examples exist
                        const sentence1 = w.example || "";
                        const sentence2 = w.long_example || "";
                        const hasExamples = sentence1 || sentence2;
                        
                        // Format according to word casing settings
                        const displayWord = formatWordBySetting(w.word);
                        
                        const isWordLearned = learnedSet.has(w.word.trim().toLowerCase());
                        const learnedClass = isWordLearned ? " learned" : "";

                        const cleanWord = w.word.trim().toLowerCase();
                        const statusEntry = wordStatuses[cleanWord];
                        
                        let statusType = 'notseen';
                        if (isWordLearned || (statusEntry && statusEntry.status === 'mastered')) {
                            statusType = 'mastered';
                        } else if ((w.word in missedWordsDB) || (cleanWord in missedWordsDB) || (statusEntry && statusEntry.status === 'bookmarked')) {
                            statusType = 'review';
                        }

                        return `
                            <div class="library-word-card p-4 sm:p-5 flex flex-col gap-3 transition-colors duration-200 cursor-pointer${learnedClass}" data-status="${statusType}" onpointerdown="handleLibraryWordPointerDown(event, this, '${w.word.replace(/'/g, "\\'")}')" onpointerup="handleLibraryWordPointerUp(event, this, '${w.word.replace(/'/g, "\\'")}')">
                                <div class="flex items-start justify-between gap-3 w-full">
                                    <div class="flex flex-wrap items-baseline gap-x-2.5 gap-y-1">
                                        <h3 class="text-lg sm:text-xl font-bold font-serif text-slate-800 dark:text-white flex items-center gap-1.5">
                                            <span>${displayWord}</span>
                                            <svg class="w-4 h-4 text-emerald-600 dark:text-emerald-400 hidden learned-check-icon shrink-0" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="3" d="M5 13l4 4L19 7"></path></svg>
                                        </h3>
                                        <span class="px-2 py-0.5 bg-slate-100 dark:bg-neutral-800 border border-slate-200 dark:border-neutral-700 rounded-full text-xs text-slate-500 dark:text-slate-400 font-mono italic">${w.type}</span>
                                    </div>
                                    ${hasExamples ? `
                                        <button onclick="toggleLibraryWordExamples(this, '${wordId}')" class="shrink-0 px-3 py-1 bg-slate-100 hover:bg-slate-200 dark:bg-neutral-800 dark:hover:bg-neutral-700 border border-slate-200 dark:border-neutral-700 rounded-full text-xs font-semibold text-slate-600 dark:text-slate-300 transition-colors focus:outline-none inline-flex items-center gap-1.5">
                                            <span class="hidden sm:inline">Show Examples</span>
                                            <span class="inline sm:hidden [@media(max-width:350px)]:hidden">Examples</span>
                                            <span class="[@media(max-width:350px)]:inline hidden">Ex.</span>
                                            <svg class="w-3.5 h-3.5 transform transition-transform duration-200" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2.5" d="M19 9l-7 7-7-7"></path></svg>
                                        </button>
                                    ` : ''}
                                </div>
                                <div class="text-sm sm:text-[15px] text-slate-700 dark:text-slate-200 leading-relaxed font-medium">
                                    ${w.def}
                                </div>
                                
                                ${hasExamples ? `
                                    <div id="${wordId}" class="hidden flex flex-col gap-3 border-t border-slate-100 dark:border-neutral-800 pt-3 mt-1 fade-in-slow">
                                        ${sentence1 ? `
                                            <div class="pl-3.5 border-l-2 border-slate-300 dark:border-white">
                                                <p class="text-xs font-semibold text-slate-400 dark:text-slate-500 uppercase tracking-wider mb-0.5">Example 1</p>
                                                <p class="font-serif italic text-sm sm:text-base text-slate-800 dark:text-slate-200 leading-relaxed">${sentence1}</p>
                                            </div>
                                        ` : ''}
                                        ${sentence2 ? `
                                            <div class="pl-3.5 border-l-2 border-primary-500 dark:border-primary-600">
                                                <p class="text-xs font-semibold text-slate-400 dark:text-slate-500 uppercase tracking-wider mb-0.5">Example 2</p>
                                                <p class="font-serif italic text-sm sm:text-base text-slate-800 dark:text-slate-200 leading-relaxed">${sentence2}</p>
                                            </div>
                                        ` : ''}
                                    </div>
                                ` : ''}
                            </div>
                        `;
                    }).join('')}
                </div>
            `;
            container.innerHTML = listHTML;
        }

        function filterLibraryWords(val) {
            const cards = document.querySelectorAll('.library-word-card');
            let visibleCount = 0;
            cards.forEach(card => {
                const status = card.dataset.status;
                if (val === 'all' || status === val) {
                    card.classList.remove('hidden');
                    visibleCount++;
                } else {
                    card.classList.add('hidden');
                }
            });
            const countEl = document.getElementById('library-word-count');
            if (countEl) {
                const suffix = visibleCount === 1 ? 'Word' : 'Words';
                if (val === 'all') {
                    countEl.innerText = `${visibleCount} ${suffix} in Book`;
                } else if (val === 'mastered') {
                    countEl.innerText = `${visibleCount} Mastered ${suffix}`;
                } else if (val === 'review') {
                    countEl.innerText = `${visibleCount} ${suffix} in Review`;
                } else if (val === 'notseen') {
                    countEl.innerText = `${visibleCount} Not Seen ${suffix}`;
                }
            }
        }

        function toggleSyncMasteredToLearned(checked) {
            localStorage.setItem('greSyncMasteredToLearned', checked ? 'true' : 'false');
            if (checked) {
                syncAllMasteredToLearned();
            }
        }

        function syncAllMasteredToLearned() {
            const learnedList = safeLocalStorageGetJSON('learned-words', []);
            const learnedSet = new Set(learnedList.map(w => w.trim().toLowerCase()));
            let changed = false;

            // 1. Check greWordStatuses
            const wordStatuses = safeLocalStorageGetJSON('greWordStatuses', {});
            for (const word in wordStatuses) {
                if (wordStatuses[word].status === 'mastered') {
                    const cleanWord = word.trim().toLowerCase();
                    if (!learnedSet.has(cleanWord)) {
                        learnedSet.add(cleanWord);
                        changed = true;
                    }
                }
            }

            // 2. Check vocabularyDB for isMasteredWord
            Object.keys(vocabularyDB).forEach(cat => {
                Object.keys(vocabularyDB[cat]).forEach(set => {
                    vocabularyDB[cat][set].forEach(w => {
                        if (isMasteredWord(w)) {
                            const cleanWord = w.word.trim().toLowerCase();
                            if (!learnedSet.has(cleanWord)) {
                                learnedSet.add(cleanWord);
                                changed = true;
                            }
                        }
                    });
                });
            });

            if (changed) {
                localStorage.setItem('learned-words', JSON.stringify(Array.from(learnedSet)));
                hasUnsavedChanges = true;
                pushToCloud();
                showToast("Mastered words synced to learned list", "success");
            }
        }

        function getUnsyncedMasteredCount() {
            const learnedList = safeLocalStorageGetJSON('learned-words', []);
            const learnedSet = new Set(learnedList.map(w => w.trim().toLowerCase()));
            const masteredSet = new Set();

            const wordStatuses = safeLocalStorageGetJSON('greWordStatuses', {});
            for (const word in wordStatuses) {
                if (wordStatuses[word].status === 'mastered') {
                    masteredSet.add(word.trim().toLowerCase());
                }
            }

            Object.keys(vocabularyDB).forEach(cat => {
                Object.keys(vocabularyDB[cat]).forEach(set => {
                    vocabularyDB[cat][set].forEach(w => {
                        if (isMasteredWord(w)) {
                            masteredSet.add(w.word.trim().toLowerCase());
                        }
                    });
                });
            });

            let count = 0;
            masteredSet.forEach(w => {
                if (!learnedSet.has(w)) {
                    count++;
                }
            });
            return count;
        }

        function renderLibrarySubActions() {
            const actionsContainer = document.getElementById('library-sub-actions');
            if (!actionsContainer) return;
            
            const isEnabled = localStorage.getItem('greSyncMasteredToLearned') === 'true';
            
            actionsContainer.innerHTML = `
                <div class="flex items-center gap-2">
                    <label class="relative inline-flex items-center cursor-pointer flex-shrink-0" style="-webkit-tap-highlight-color: transparent;">
                        <input type="checkbox" switch id="setting-sync-mastered" onchange="haptic(); handleSyncMasteredClick(this.checked)" class="sr-only peer" ${isEnabled ? 'checked' : ''}>
                        <div class="w-11 h-6 bg-slate-200 dark:bg-neutral-800 rounded-full peer peer-checked:after:translate-x-full after:content-[''] after:absolute after:top-0.5 after:left-[2px] after:bg-white after:border-slate-300 dark:after:border-slate-600 after:border after:rounded-full after:h-5 after:w-5 after:transition-all peer-checked:bg-emerald-500"></div>
                    </label>
                    
                    <div class="relative inline-block">
                        <button id="sync-help-btn"
                            onmouseenter="showLibraryTooltip()" onmouseleave="hideLibraryTooltip()" ontouchstart="showLibraryTooltipTouch()"
                            class="flex items-center justify-center w-5 h-5 rounded-full border border-slate-300 dark:border-neutral-700 text-slate-500 dark:text-slate-400 text-[10px] font-bold transition-colors focus:outline-none hover:bg-slate-50 dark:hover:bg-neutral-800"
                            style="-webkit-tap-highlight-color: transparent;">
                            ?
                        </button>
                        <div id="library-tooltip" class="absolute top-full right-0 mt-2 w-48 sm:w-56 z-[250] bg-slate-800 dark:bg-neutral-800 text-slate-100 text-xs font-medium rounded-lg py-2 px-3 shadow-xl border border-slate-700 dark:border-neutral-700 opacity-0 pointer-events-none transition-opacity duration-150 text-left leading-normal whitespace-normal">
                            Mark past and future mastered words as learned
                        </div>
                    </div>
                </div>
            `;
        }

        function handleSyncMasteredClick(checked) {
            setTimeout(() => {
                const isEnabled = localStorage.getItem('greSyncMasteredToLearned') === 'true';
                if (checked) {
                    const count = getUnsyncedMasteredCount();
                    if (confirm(`Mark past and future mastered words in any game mode as learned? This will mark ${count} words as learned.`)) {
                        toggleSyncMasteredToLearned(true);
                        renderLibrarySubActions();
                    } else {
                        const cb = document.getElementById('setting-sync-mastered');
                        if (cb) cb.checked = false;
                    }
                } else {
                    if (confirm("Stop marking future mastered words as learned?")) {
                        toggleSyncMasteredToLearned(false);
                        renderLibrarySubActions();
                    } else {
                        const cb = document.getElementById('setting-sync-mastered');
                        if (cb) cb.checked = true;
                    }
                }
            }, 50);
        }

        let tooltipTimeout = null;
        function showLibraryTooltip() {
            const tooltip = document.getElementById('library-tooltip');
            if (tooltip) {
                if (tooltipTimeout) { clearTimeout(tooltipTimeout); tooltipTimeout = null; }
                tooltip.classList.remove('opacity-0', 'pointer-events-none');
                tooltip.classList.add('opacity-100');
            }
        }

        function hideLibraryTooltip() {
            const tooltip = document.getElementById('library-tooltip');
            if (tooltip) {
                tooltip.classList.remove('opacity-100');
                tooltip.classList.add('opacity-0', 'pointer-events-none');
            }
        }

        function showLibraryTooltipTouch() {
            showLibraryTooltip();
            if (tooltipTimeout) clearTimeout(tooltipTimeout);
            tooltipTimeout = setTimeout(() => {
                hideLibraryTooltip();
            }, 3000);
        }

        function handleLibraryWordPointerDown(event, cardEl, word) {
            if (event.target.closest('button') || event.target.closest('a')) {
                return;
            }
            if (!event.isPrimary) return;
            cardEl.dataset.startX = event.clientX.toString();
            cardEl.dataset.startY = event.clientY.toString();
            cardEl.dataset.tapTime = Date.now().toString();
        }

        function handleLibraryWordPointerUp(event, cardEl, word) {
            if (event.target.closest('button') || event.target.closest('a')) {
                return;
            }
            if (!event.isPrimary) return;

            const startX = parseFloat(cardEl.dataset.startX || '0');
            const startY = parseFloat(cardEl.dataset.startY || '0');
            const tapTime = parseInt(cardEl.dataset.tapTime || '0', 10);
            
            const dist = Math.hypot(event.clientX - startX, event.clientY - startY);
            const duration = Date.now() - tapTime;
            
            // If they moved less than 12px (not scrolling) and lifted within 250ms (clean tap)
            if (dist < 12 && duration < 250) {
                const now = Date.now();
                const lastTap = parseInt(cardEl.dataset.lastTap || '0', 10);
                
                if (now - lastTap < 300) {
                    toggleLibraryWordLearned(cardEl, word);
                    cardEl.dataset.lastTap = '0'; // Reset so subsequent taps don't toggle immediately
                } else {
                    cardEl.dataset.lastTap = now.toString();
                }
            }
        }

        function toggleLibraryWordLearned(cardEl, word) {
            const cleanWord = word.trim().toLowerCase();
            const learnedList = safeLocalStorageGetJSON('learned-words', []);
            const learnedSet = new Set(learnedList.map(w => w.trim().toLowerCase()));

            if (learnedSet.has(cleanWord)) {
                learnedSet.delete(cleanWord);
                cardEl.classList.remove('learned');
            } else {
                learnedSet.add(cleanWord);
                cardEl.classList.add('learned');
            }

            localStorage.setItem('learned-words', JSON.stringify(Array.from(learnedSet)));
            hasUnsavedChanges = true;
            pushToCloud();
            haptic();
        }

        function toggleLibraryWordExamples(btn, elementId, forceState) {
            const el = document.getElementById(elementId);
            if (!el) return;
            const svg = btn.querySelector('svg');
            const spans = btn.querySelectorAll('span');

            const isCurrentlyHidden = el.classList.contains('hidden');
            const shouldShow = forceState !== undefined ? forceState : isCurrentlyHidden;

            if (shouldShow) {
                el.classList.remove('hidden');
                if (spans[0]) spans[0].innerText = "Hide Examples";
                if (spans[1]) spans[1].innerText = "Hide";
                if (spans[2]) spans[2].innerText = "Hide";
                if (svg) svg.classList.add('rotate-180');
            } else {
                el.classList.add('hidden');
                if (spans[0]) spans[0].innerText = "Show Examples";
                if (spans[1]) spans[1].innerText = "Examples";
                if (spans[2]) spans[2].innerText = "Ex.";
                if (svg) svg.classList.remove('rotate-180');
            }
        }

        function toggleAllLibraryExamples(btn) {
            const allCards = document.querySelectorAll('.library-word-card');
            const expandAll = btn.innerText.includes('Expand');

            allCards.forEach(card => {
                const toggleBtn = card.querySelector('button[onclick^="toggleLibraryWordExamples"]');
                const exContainer = card.querySelector('[id^="lib-word-ex-"]');
                if (toggleBtn && exContainer) {
                    toggleLibraryWordExamples(toggleBtn, exContainer.id, expandAll);
                }
            });

            if (expandAll) {
                btn.innerText = "Collapse All Examples";
                btn.classList.remove('bg-primary-600', 'hover:bg-primary-700');
                btn.classList.add('bg-slate-600', 'hover:bg-slate-700');
            } else {
                btn.innerText = "Expand All Examples";
                btn.classList.add('bg-primary-600', 'hover:bg-primary-700');
                btn.classList.remove('bg-slate-600', 'hover:bg-slate-700');
            }
        }

        function haptic() {
            if (navigator.vibrate) navigator.vibrate(10);
        }
        function showToast(message, type) {
            const toast = document.createElement('div');
            const colors = type === 'success'
                ? 'bg-emerald-600 text-white'
                : type === 'error'
                    ? 'bg-rose-600 text-white'
                    : 'bg-slate-700 text-white';
            toast.className = 'fixed left-1/2 -translate-x-1/2 z-[200] px-5 py-3 rounded-xl shadow-2xl text-sm font-semibold ' + colors;
            toast.style.top = 'calc(env(safe-area-inset-top) + 4.5rem)';
            toast.textContent = message;
            toast.style.transition = 'opacity 0.3s ease, transform 0.3s ease';
            toast.style.opacity = '1';
            document.body.appendChild(toast);
            setTimeout(() => {
                toast.style.opacity = '0';
                toast.style.transform = 'translateX(-50%) translateY(-10px)';
                setTimeout(() => toast.remove(), 300);
            }, 1500);
        }
        function initHapticOverlays() {
            const isIOS = /iPad|iPhone|iPod/.test(navigator.userAgent)
                || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
            if (!isIOS) return;
            document.querySelectorAll('[data-haptic]').forEach(el => {
                if (el.querySelector('[data-haptic-trigger]')) return;
                const sw = document.createElement('input');
                sw.type = 'checkbox';
                sw.setAttribute('switch', '');
                sw.setAttribute('data-haptic-trigger', '');
                sw.setAttribute('aria-hidden', 'true');
                sw.tabIndex = -1;
                Object.assign(sw.style, {
                    position: 'absolute', inset: '0', width: '100%', height: '100%',
                    margin: '0', opacity: '0', clipPath: 'inset(0 round 999px)',
                    touchAction: 'manipulation', zIndex: '9999'
                });
                sw.style.setProperty('-webkit-tap-highlight-color', 'transparent');
                if (getComputedStyle(el).position === 'static') el.style.position = 'relative';
                el.appendChild(sw);
            });
        }

        function toggleSettings() {
            const isHidden = document.getElementById('settings-screen').classList.contains('hidden');
            if (isHidden) {
                if (_navStack.includes('study-screen') && !confirm('Leave your current study session and go to Settings? Progress will be saved.')) {
                    return;
                }
                _navStack.push('settings-screen');
                initSettings();
                _showScreen('settings-screen');
            } else {
                showSetup();
            }
        }

        function toggleDashboardModal() {
            const isHidden = document.getElementById('dashboard-screen').classList.contains('hidden');
            if (isHidden) {
                if (_navStack.includes('study-screen') && !confirm('Leave your current study session and go to Dashboard? Progress will be saved.')) {
                    return;
                }
                _navStack.push('dashboard-screen');
                updateDashboard();
                _showScreen('dashboard-screen');
            } else {
                showSetup();
            }
        }

        initThemeIcon(); 

        // =========================================================
        // 2.5 CLOUD SYNC LOGIC
        // =========================================================
        const SUPABASE_URL = "https://ejxiptrgbcqezleafbcy.supabase.co";
        const SUPABASE_ANON_KEY = "sb_publishable_qhoYqU_u2FXCVnGvt64Thw_D9eADKqf";
        const CLOUD_PREFIX = "d5107002710815f8b57d323e7c84997619ed04b3074d122fa2d2238000a7eaac";

        function randomBase36(len = 6) {
            const chars = '0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ';
            const bytes = new Uint8Array(len);
            crypto.getRandomValues(bytes);
            let out = '';
            for (let i = 0; i < len; i++) out += chars[bytes[i] % chars.length];
            return out;
        }

        function getCloudKey() {
            let key = localStorage.getItem('greCloudKey');
            if (!key) {
                key = 'gre-' + randomBase36(6) + '-' + randomBase36(5) + '-' + randomBase36(6);
                localStorage.setItem('greCloudKey', key);
                const el = document.getElementById('setting-cloud-key');
                if (el) el.textContent = key;
            }
            return key;
        }

        async function sha256(message) {
            if (!message || message === 'public') return 'public';
            const msgBuffer = new TextEncoder().encode(message);
            const hashBuffer = await crypto.subtle.digest('SHA-256', msgBuffer);
            const hashArray = Array.from(new Uint8Array(hashBuffer));
            return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
        }

        async function pushToCloud() {
            if (localStorage.getItem('greCloudSyncEnabled') !== 'true') return;
            if (!hasUnsavedChanges) return;
            if (!SUPABASE_URL || SUPABASE_URL === "YOUR_SUPABASE_URL_HERE" || !SUPABASE_ANON_KEY || SUPABASE_ANON_KEY === "YOUR_SUPABASE_ANON_KEY_HERE") return;
            const cloudKey = getCloudKey();
            const data = {
                progressDB: safeLocalStorageGetJSON('greProgressDB', {}),
                missedWordsDB: safeLocalStorageGetJSON('greMissedWords', {}),
                learnedWords: safeLocalStorageGetJSON('learned-words', []),
                wordStatuses: safeLocalStorageGetJSON('greWordStatuses', {}),
                gamification: {
                    streak: localStorage.getItem('greStreak') || '0',
                    wordsToday: localStorage.getItem('greWordsLearnedToday') || '0',
                    lastDate: localStorage.getItem('greLastStudyDate') || ''
                },
                settings: {
                    wordCase: localStorage.getItem('greWordCase'),
                    autoShow: localStorage.getItem('greAutoShowSentences'),
                    autoPronounce: localStorage.getItem('greAutoPronounce'),
                    theme: localStorage.getItem('greTheme'),
                    syncMasteredToLearned: localStorage.getItem('greSyncMasteredToLearned')
                },
                lastUpdated: Date.now()
            };

            try {
                const cloudKeyHash = await sha256(cloudKey);
                const fullKey = CLOUD_PREFIX + '/' + cloudKeyHash;
                const res = await fetch(`${SUPABASE_URL}/rest/v1/user_progress?on_conflict=key_hash`, {
                    method: 'POST',
                    headers: {
                        'Content-Type': 'application/json',
                        'apikey': SUPABASE_ANON_KEY,
                        'Authorization': `Bearer ${SUPABASE_ANON_KEY}`,
                        'Prefer': 'resolution=merge-duplicates'
                    },
                    body: JSON.stringify({
                        key_hash: fullKey,
                        data: data,
                        last_updated: data.lastUpdated
                    })
                });
                if (!res.ok) {
                    throw new Error(`Supabase push failed with status ${res.status}`);
                }
                hasUnsavedChanges = false;
            } catch (err) {
                console.error("Failed to sync to cloud:", err);
            }
        }

        // Auto-sync when app is closed, hidden or navigated away
        document.addEventListener("visibilitychange", () => {
            if (document.visibilityState === 'hidden') {
                pushToCloud();
            }
        });

        window.addEventListener("pagehide", () => {
            pushToCloud();
        });

        async function pullFromCloud(cloudKey) {
            if (!cloudKey || !SUPABASE_URL || SUPABASE_URL === "YOUR_SUPABASE_URL_HERE" || !SUPABASE_ANON_KEY || SUPABASE_ANON_KEY === "YOUR_SUPABASE_ANON_KEY_HERE") return false;
            try {
                const cloudKeyHash = await sha256(cloudKey);
                const fullKey = CLOUD_PREFIX + '/' + cloudKeyHash;
                const res = await fetch(`${SUPABASE_URL}/rest/v1/user_progress?key_hash=eq.${fullKey}&select=data`, {
                    method: 'GET',
                    headers: {
                        'apikey': SUPABASE_ANON_KEY,
                        'Authorization': `Bearer ${SUPABASE_ANON_KEY}`
                    }
                });
                if (!res.ok) throw new Error(`Supabase pull failed with status ${res.status}`);
                const rows = await res.json();
                if (rows && rows.length > 0) {
                    const data = rows[0].data;
                    if (data) {
                        if (data.progressDB && Object.keys(data.progressDB).length > 0) {
                            localStorage.setItem('greProgressDB', JSON.stringify(data.progressDB));
                            progressDB = data.progressDB;
                        } else {
                            localStorage.removeItem('greProgressDB');
                            progressDB = {};
                        }
                        if (data.missedWordsDB && Object.keys(data.missedWordsDB).length > 0) {
                            migrateMissedWordsToIndexes(data.missedWordsDB);
                            localStorage.setItem('greMissedWords', JSON.stringify(data.missedWordsDB));
                            missedWordsDB = data.missedWordsDB;
                        } else {
                            localStorage.removeItem('greMissedWords');
                            missedWordsDB = {};
                        }
                        if (data.learnedWords) {
                            localStorage.setItem('learned-words', JSON.stringify(data.learnedWords));
                        } else {
                            localStorage.removeItem('learned-words');
                        }
                        if (data.wordStatuses) {
                            localStorage.setItem('greWordStatuses', JSON.stringify(data.wordStatuses));
                        } else {
                            localStorage.removeItem('greWordStatuses');
                        }
                        if (data.gamification) {
                            if (data.gamification.streak) localStorage.setItem('greStreak', data.gamification.streak);
                            if (data.gamification.wordsToday) localStorage.setItem('greWordsLearnedToday', data.gamification.wordsToday);
                            if (data.gamification.lastDate) localStorage.setItem('greLastStudyDate', data.gamification.lastDate);
                            if (typeof initGamification === 'function') initGamification();
                        }
                        if (data.settings) {
                            if (data.settings.wordCase) localStorage.setItem('greWordCase', data.settings.wordCase);
                            if (data.settings.autoShow !== undefined) localStorage.setItem('greAutoShowSentences', data.settings.autoShow);
                            if (data.settings.autoPronounce !== undefined) localStorage.setItem('greAutoPronounce', data.settings.autoPronounce);
                            if (data.settings.syncMasteredToLearned !== undefined) localStorage.setItem('greSyncMasteredToLearned', data.settings.syncMasteredToLearned);
                        }
                        hasUnsavedChanges = false;
                        return true;
                    }
                }
            } catch (err) {
                console.error("Failed to pull from cloud:", err);
            }
            return false;
        }

        async function handleUrlSync() {
            const params = new URLSearchParams(window.location.search);
            const syncKey = params.get('key') || params.get('sync');
            if (!syncKey) return;

            // Strip the sync param immediately so refreshing, bookmarking, or
            // re-sharing this tab's current URL doesn't repeat this flow.
            window.history.replaceState({}, document.title, window.location.pathname);

            if (!SUPABASE_URL || SUPABASE_URL === "YOUR_SUPABASE_URL_HERE" || !SUPABASE_ANON_KEY || SUPABASE_ANON_KEY === "YOUR_SUPABASE_ANON_KEY_HERE") {
                alert("Cloud sync isn't configured for this app, so this link can't be used.");
                return;
            }

            const currentKey = localStorage.getItem('greCloudKey');
            const isDifferentAccount = currentKey && currentKey !== syncKey;

            // Only show the warning when this link would move this device onto a
            // DIFFERENT sync account than it's already using, since that's the
            // scenario that entangles two people's progress going forward.
            if (isDifferentAccount) {
                const proceed = confirm(
                    "This link will connect this device to a different Cloud Sync account than the one it's currently using.\n\n" +
                    "Your existing local progress will be merged (not deleted) with the linked account's data, and from now on this device will keep syncing to that account instead.\n\n" +
                    "Only continue if you trust this link. Continue?"
                );
                if (!proceed) return;
            }

            let success = false;
            try {
                // Merge instead of blindly overwriting, so local progress is
                // never silently destroyed by an untrusted or stale link.
                success = await pullAndMergeCloud(syncKey);
            } catch (err) {
                console.error("Sync link failed:", err);
                success = false;
            }

            if (success) {
                localStorage.setItem('greCloudKey', syncKey);
                localStorage.setItem('greCloudSyncEnabled', 'true');
                hasUnsavedChanges = true;
                await pushToCloud();
                alert("Successfully synced progress from the linked device!");
                window.location.reload();
            } else {
                alert("Failed to sync using this link. Your local progress hasn't been changed, and cloud sync hasn't been enabled.");
            }
        }

        async function silentInitialPull() {
            if (localStorage.getItem('greCloudSyncEnabled') !== 'true') return;
            const cloudKey = getCloudKey();
            if (!cloudKey || !SUPABASE_URL || SUPABASE_URL === "YOUR_SUPABASE_URL_HERE" || !SUPABASE_ANON_KEY || SUPABASE_ANON_KEY === "YOUR_SUPABASE_ANON_KEY_HERE") return;
            const success = await pullFromCloud(cloudKey);
            if (success) {
                if (typeof updateMissedUI === 'function') updateMissedUI();
                if (typeof updateSetOptions === 'function') updateSetOptions();
                initSettings();
            }
        }

        // Initialize sync on load
        handleUrlSync();
        silentInitialPull();

        // =========================================================
        // 3. SETTINGS & RESET
        // =========================================================
        function showNavControls() {
            const navControls = document.getElementById('nav-controls');
            if (navControls && mode === 'flashcard') {
                navControls.classList.remove('opacity-0', 'pointer-events-none', 'h-2', 'overflow-hidden');
                navControls.classList.add('opacity-100', 'pointer-events-none', 'h-14', 'mt-4', 'mb-2');
            }
        }

        function hideNavControls() {
            const navControls = document.getElementById('nav-controls');
            if (navControls) {
                navControls.classList.add('opacity-0', 'pointer-events-none', 'h-2', 'overflow-hidden');
                navControls.classList.remove('opacity-100', 'pointer-events-auto', 'h-14', 'mt-4', 'mb-2');
            }
        }

        function initSettings() {
            const wordCaseSetting = localStorage.getItem('greWordCase') || 'lowercase';
            document.getElementById('setting-word-case').value = wordCaseSetting;
            
            const autoShowSetting = localStorage.getItem('greAutoShowSentences') === 'true';
            document.getElementById('setting-auto-show-sentences').checked = autoShowSetting;
            
            const autoPronounceSetting = localStorage.getItem('greAutoPronounce') === 'true';
            document.getElementById('setting-auto-pronounce').checked = autoPronounceSetting;
            
            const cloudSyncEnabled = localStorage.getItem('greCloudSyncEnabled') === 'true';
            const enableCloudToggle = document.getElementById('setting-enable-cloud');
            if (enableCloudToggle) enableCloudToggle.checked = cloudSyncEnabled;
            
            const cloudKeyContainer = document.getElementById('cloud-key-container');
            if (cloudKeyContainer) {
                if (cloudSyncEnabled) {
                    cloudKeyContainer.classList.remove('hidden');
                } else {
                    cloudKeyContainer.classList.add('hidden');
                }
            }
            
            const cloudKeySetting = localStorage.getItem('greCloudKey') || '';
            const cloudKeyEl = document.getElementById('setting-cloud-key');
            if (cloudKeyEl) cloudKeyEl.textContent = cloudKeySetting || '\u00a0';
            
            let themeSetting = localStorage.getItem('greTheme') || 'default';
            if (themeSetting === 'turquoise') {
                themeSetting = 'default';
                localStorage.setItem('greTheme', 'default');
            }
            changeTheme(themeSetting, true);
        }

        function changeTheme(themeName, init = false) {
            if (!init) {
                localStorage.setItem('greTheme', themeName);
                hasUnsavedChanges = true;
            }
            if (themeName === 'default') {
                document.documentElement.removeAttribute('data-theme');
            } else {
                document.documentElement.setAttribute('data-theme', themeName);
            }
            updateThemeToggle(themeName);
        }

        function updateThemeToggle(themeName) {
            const slider = document.getElementById('theme-slider');
            const btnDefault = document.getElementById('theme-btn-default');
            const btnIndigo = document.getElementById('theme-btn-indigo');
            if (!slider) return;
            const isIndigo = themeName === 'indigo';
            if (isIndigo) {
                slider.style.left = 'calc(100% - 36px)';
                btnDefault.classList.remove('active');
                btnIndigo.classList.add('active');
            } else {
                slider.style.left = '4px';
                btnIndigo.classList.remove('active');
                btnDefault.classList.add('active');
            }
        }
	
	async function getCloudPrefix() {
            const raw = '26d5e52abc5366c9ff9a1edf0dbdc6be1c2677331debfa113b1949b944a22b25';
            const upper = raw.toUpperCase();
            return await sha256(upper);
	}
		
        async function pullAndMergeCloud(cloudKey) {
            if (!cloudKey || !SUPABASE_URL || SUPABASE_URL === "YOUR_SUPABASE_URL_HERE" || !SUPABASE_ANON_KEY || SUPABASE_ANON_KEY === "YOUR_SUPABASE_ANON_KEY_HERE") return false;
            try {
                const cloudKeyHash = await sha256(cloudKey);
                const fullKey = CLOUD_PREFIX + '/' + cloudKeyHash;
                const res = await fetch(`${SUPABASE_URL}/rest/v1/user_progress?key_hash=eq.${fullKey}&select=data`, {
                    method: 'GET',
                    headers: {
                        'apikey': SUPABASE_ANON_KEY,
                        'Authorization': `Bearer ${SUPABASE_ANON_KEY}`
                    }
                });
                if (!res.ok) throw new Error(`Cloud request failed with status ${res.status}`);
                const rows = await res.json();
                if (rows && rows.length > 0) {
                    const data = rows[0].data;
                    if (data) {
                    // 1. Merge progressDB: take the max progress for each set
                    let mergedProgress = safeLocalStorageGetJSON('greProgressDB', {});
                    if (data.progressDB) {
                        for (const key in data.progressDB) {
                            const cloudVal = data.progressDB[key];
                            const localVal = mergedProgress[key];

                            if (key.startsWith('RM_')) {
                                // Random-mode "mastered" flags are booleans, not counters.
                                // Merge as logical OR so a mastery flag is never lost.
                                mergedProgress[key] = Boolean(cloudVal) || Boolean(localVal);
                            } else if (key.endsWith('_matched')) {
                                // Drag Match resume state is an array of matched indices.
                                // Merge as a set union instead of running it through parseInt.
                                const cloudArr = Array.isArray(cloudVal) ? cloudVal : [];
                                const localArr = Array.isArray(localVal) ? localVal : [];
                                mergedProgress[key] = Array.from(new Set([...cloudArr, ...localArr]));
                            } else if (cloudVal === 'COMPLETED' || localVal === 'COMPLETED') {
                                mergedProgress[key] = 'COMPLETED';
                            } else {
                                const cloudNum = parseInt(cloudVal) || 0;
                                const localNum = parseInt(localVal) || 0;
                                mergedProgress[key] = Math.max(cloudNum, localNum);
                            }
                        }
                    }
                    localStorage.setItem('greProgressDB', JSON.stringify(mergedProgress));
                    progressDB = mergedProgress;

                    // 2. Merge missedWordsDB: union of both lists
                    let mergedMissed = safeLocalStorageGetJSON('greMissedWords', {});
                    if (data.missedWordsDB) {
                        migrateMissedWordsToIndexes(data.missedWordsDB);
                        mergedMissed = { ...data.missedWordsDB, ...mergedMissed };
                    }
                    localStorage.setItem('greMissedWords', JSON.stringify(mergedMissed));
                    missedWordsDB = mergedMissed;

                    // Merge learned-words: union of both lists
                    let mergedLearned = new Set(safeLocalStorageGetJSON('learned-words', []));
                    if (data.learnedWords) {
                        data.learnedWords.forEach(w => mergedLearned.add(w));
                    }
                    localStorage.setItem('learned-words', JSON.stringify(Array.from(mergedLearned)));

                    // Merge wordStatuses: merge by comparing timestamps
                    let mergedWordStatuses = safeLocalStorageGetJSON('greWordStatuses', {});
                    if (data.wordStatuses) {
                        for (const w in data.wordStatuses) {
                            const cloudEntry = data.wordStatuses[w];
                            const localEntry = mergedWordStatuses[w];
                            if (!localEntry || (cloudEntry.timestamp && (!localEntry.timestamp || cloudEntry.timestamp > localEntry.timestamp))) {
                                mergedWordStatuses[w] = cloudEntry;
                            }
                        }
                    }
                    localStorage.setItem('greWordStatuses', JSON.stringify(mergedWordStatuses));

                    if (data.gamification) {
                        const cDate = data.gamification.lastDate;
                        const lDate = localStorage.getItem('greLastStudyDate');
                        if (cDate && (!lDate || new Date(cDate) > new Date(lDate) || (cDate === lDate && parseInt(data.gamification.wordsToday) > parseInt(localStorage.getItem('greWordsLearnedToday') || '0')))) {
                            localStorage.setItem('greStreak', data.gamification.streak);
                            localStorage.setItem('greWordsLearnedToday', data.gamification.wordsToday);
                            localStorage.setItem('greLastStudyDate', cDate);
                            if (typeof initGamification === 'function') initGamification();
                        }
                    }

                    // 3. Merge settings: use cloud settings if available
                    if (data.settings) {
                        if (data.settings.wordCase) localStorage.setItem('greWordCase', data.settings.wordCase);
                        if (data.settings.autoShow !== undefined) localStorage.setItem('greAutoShowSentences', data.settings.autoShow);
                        if (data.settings.autoPronounce !== undefined) localStorage.setItem('greAutoPronounce', data.settings.autoPronounce);
                        if (data.settings.theme) localStorage.setItem('greTheme', data.settings.theme);
                        if (data.settings.syncMasteredToLearned !== undefined) localStorage.setItem('greSyncMasteredToLearned', data.settings.syncMasteredToLearned);
                    }
                }
            }

            // Update UI to match the newly merged state
            if (typeof updateMissedUI === 'function') updateMissedUI();
            if (typeof updateSetOptions === 'function') updateSetOptions();
            initSettings();
            return true;
            } catch (err) {
                console.error("Failed to pull and merge from cloud:", err);
                return false;
            }
        }

        async function copyCloudKey() {
            const el = document.getElementById('setting-cloud-key');
            const key = (el.textContent || '').trim();
            if (!key) return;
            try {
                await navigator.clipboard.writeText(key);
                const btn = el.parentElement.querySelector('button');
                const origHTML = btn.innerHTML;
                btn.innerHTML = '<svg class="w-4 h-4 text-emerald-500" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2.5" d="M5 13l4 4L19 7"></path></svg>';
                setTimeout(() => { btn.innerHTML = origHTML; }, 1200);
            } catch(e) {}
        }

        async function toggleCloudSync(checked) {
            const container = document.getElementById('cloud-key-container');
            if (checked) {
                // Fetch current active key or generate a temporary layout choice without writing to storage yet
                let cloudKey = localStorage.getItem('greCloudKey');
                if (!cloudKey) {
                    cloudKey = 'gre-' + randomBase36(6) + '-' + randomBase36(5) + '-' + randomBase36(6);
                }
                
                const keyInput = document.getElementById('cloud-confirm-key-input');
                if (keyInput) keyInput.value = cloudKey;

                // Display popup safely
                const modal = document.getElementById('cloud-confirm-modal');
                if (modal) {
                    modal.classList.remove('hidden');
                    modal.classList.add('flex');
                    document.querySelector('main').style.pointerEvents = 'none';
                }
                
                const errorDiv = document.getElementById('cloud-confirm-error');
                if (errorDiv) errorDiv.classList.add('hidden');
                
                // Retain unverified switch state until approved
                document.getElementById('setting-enable-cloud').checked = false;
            } else {
                localStorage.setItem('greCloudSyncEnabled', 'false');
                if (container) container.classList.add('hidden');
            }
        }

        function rollNewConfirmKey() {
            const keyInput = document.getElementById('cloud-confirm-key-input');
            if (keyInput) {
                keyInput.value = 'gre-' + randomBase36(6) + '-' + randomBase36(5) + '-' + randomBase36(6);
            }
        }

        function cancelCloudSyncConfirm() {
            const modal = document.getElementById('cloud-confirm-modal');
            if (modal) {
                modal.classList.add('hidden');
                modal.classList.remove('flex');
                document.querySelector('main').style.pointerEvents = '';
            }
            // Ensure the toggle is unchecked
            document.getElementById('setting-enable-cloud').checked = false;
        }

        async function acceptCloudSyncConfirm() {
            const cancelBtn = document.getElementById('cloud-confirm-cancel-btn');
            const acceptBtn = document.getElementById('cloud-confirm-accept-btn');
            const acceptText = document.getElementById('cloud-confirm-accept-text');
            const spinner = document.getElementById('cloud-confirm-spinner');
            const errorDiv = document.getElementById('cloud-confirm-error');
            
            // Get the key entered by the user
            const keyInput = document.getElementById('cloud-confirm-key-input');
            const cloudKey = keyInput ? keyInput.value.trim() : '';
            
            if (!cloudKey) {
                errorDiv.textContent = "Please enter a valid Cloud Sync Key.";
                errorDiv.classList.remove('hidden');
                return;
            }

            // Enforce desired key format validation (gre-xxxxxx-xxxxx-xxxxxx)
            const keyFormatRegex = /^gre-[a-zA-Z0-9]{6}-[a-zA-Z0-9]{5}-[a-zA-Z0-9]{6}$/;
            if (!keyFormatRegex.test(cloudKey)) {
                errorDiv.textContent = "Invalid key format! Try rolling a new one with the dice or check your existing key if you're syncing devices.";
                errorDiv.classList.remove('hidden');
                return;
            }
            
            // Set loading state
            cancelBtn.disabled = true;
            acceptBtn.disabled = true;
            cancelBtn.classList.add('opacity-50', 'pointer-events-none');
            acceptBtn.classList.add('opacity-75', 'pointer-events-none');
            acceptText.textContent = "Syncing...";
            spinner.classList.remove('hidden');
            errorDiv.classList.add('hidden');
            
            try {
                // Save this key locally first so pullAndMergeCloud and pushToCloud use the user's updated key!
                localStorage.setItem('greCloudKey', cloudKey);
                
                // Also update the key input in the main settings UI
                const mainKeyInput = document.getElementById('setting-cloud-key');
                if (mainKeyInput) mainKeyInput.textContent = cloudKey;

                const success = await pullAndMergeCloud(cloudKey);
                
                if (success) {
                    // Update state
                    localStorage.setItem('greCloudSyncEnabled', 'true');
                    document.getElementById('setting-enable-cloud').checked = true;
                    
                    const container = document.getElementById('cloud-key-container');
                    if (container) container.classList.remove('hidden');
                    
                    hasUnsavedChanges = true;
                    await pushToCloud();
                    
                    // Hide the confirmation modal
                    const modal = document.getElementById('cloud-confirm-modal');
                    if (modal) {
                        modal.classList.add('hidden');
                        modal.classList.remove('flex');
                        document.querySelector('main').style.pointerEvents = '';
                    }
                    
                    showToast("Cloud Sync enabled! Progress merged.", "success");
                } else {
                    throw new Error("Could not sync with the cloud database.");
                }
            } catch (err) {
                console.error("Failed to enable cloud sync:", err);
                errorDiv.classList.remove('hidden');
                errorDiv.textContent = "Could not sync. Please check your internet connection or try again later.";
                
                // Clean up unverified storage items on structural failure
                localStorage.removeItem('greCloudKey');
                if (mainKeyInput) mainKeyInput.value = '';
            } finally {
                // Reset loading state
                cancelBtn.disabled = false;
                acceptBtn.disabled = false;
                cancelBtn.classList.remove('opacity-50', 'pointer-events-none');
                acceptBtn.classList.remove('opacity-75', 'pointer-events-none');
                acceptText.textContent = "Enable";
                spinner.classList.add('hidden');
            }
        }

        async function changeCloudKey(val) {
            localStorage.setItem('greCloudKey', val);
            if (localStorage.getItem('greCloudSyncEnabled') === 'true') {
                const success = await pullAndMergeCloud(val);
                if (success) {
                    hasUnsavedChanges = true;
                    await pushToCloud();
                }
            }
        }

        function toggleAutoPronounce(checked) {
            localStorage.setItem('greAutoPronounce', checked);
            hasUnsavedChanges = true;
        }

        function toggleAutoShowSentences(checked) {
            localStorage.setItem('greAutoShowSentences', checked);
            hasUnsavedChanges = true;
            if (!document.getElementById('study-screen').classList.contains('hidden') && !isSessionComplete) {
                if (mode === 'mcq') {
                    isCardCollapsed = !checked;
                    const container = document.getElementById('card-container');
                    const btns = [document.getElementById('example-btn-front'), document.getElementById('example-btn-back')];
                    if (isCardCollapsed) {
                        container.classList.add('card-collapsed');
                        btns.forEach(btn => {
                            if (btn) btn.title = "Expand Card";
                        });
                    } else {
                        container.classList.remove('card-collapsed');
                        btns.forEach(btn => {
                            if (btn) btn.title = "Collapse Card";
                        });
                    }
                } else if (mode === 'flashcard') {
                    const frontExample = document.getElementById('card-front-example');
                    const currentWordObj = appData[currentIndex];
                    if (currentWordObj && currentWordObj.example) {
                        if (checked) {
                            frontExample.classList.remove('hidden');
                        } else {
                            frontExample.classList.add('hidden');
                        }
                    }
                }
            }
        }

        function changeWordCase(val) {
            localStorage.setItem('greWordCase', val);
            hasUnsavedChanges = true;
            if (!document.getElementById('study-screen').classList.contains('hidden') && !isSessionComplete) {
                applyWordCase();
            }
        }

        function applyWordCase() {
            const wordCase = localStorage.getItem('greWordCase') || 'lowercase';
            const frontWord = document.getElementById('card-front-word');
            const backWord = document.getElementById('card-back-word');
            
            frontWord.classList.remove('capitalize', 'lowercase', 'uppercase', 'normal-case');
            backWord.classList.remove('capitalize', 'lowercase', 'uppercase', 'normal-case');
            
            frontWord.classList.add(wordCase);
            backWord.classList.add(wordCase);
        }

        async function resetProgress() {
                if (!confirm('Reset all progress? This will erase your study data locally and in the cloud.')) return;
                localStorage.removeItem('greLastSeenWords');
                localStorage.removeItem('greMissedWords');
                localStorage.removeItem('greProgressDB');
                localStorage.removeItem('greStreak');
                localStorage.removeItem('greLastStudyDate');
                localStorage.removeItem('greWordsLearnedToday');
                localStorage.removeItem('learned-words');
                localStorage.removeItem('greWordStatuses');
                localStorage.removeItem('greSyncMasteredToLearned');
                missedWordsDB = {};
                progressDB = {};
                if (typeof initGamification === 'function') initGamification();
                
                // Force sync progress reset to cloud even if cloud sync is disabled
                if (SUPABASE_URL && SUPABASE_URL !== "YOUR_SUPABASE_URL_HERE" && SUPABASE_ANON_KEY && SUPABASE_ANON_KEY !== "YOUR_SUPABASE_ANON_KEY_HERE") {
                    const cloudKey = localStorage.getItem('greCloudKey') || 'public';
                    const data = {
                        progressDB: {},
                        missedWordsDB: {},
                        learnedWords: [],
                        wordStatuses: {},
                        settings: {
                            wordCase: localStorage.getItem('greWordCase'),
                            autoShow: localStorage.getItem('greAutoShowSentences'),
                            autoPronounce: localStorage.getItem('greAutoPronounce'),
                            syncMasteredToLearned: 'false',
                            cloudKey: cloudKey
                        },
                        lastUpdated: Date.now()
                    };
                    try {
                        const cloudKeyHash = await sha256(cloudKey);
                        const fullKey = CLOUD_PREFIX + '/' + cloudKeyHash;
                        await fetch(`${SUPABASE_URL}/rest/v1/user_progress?on_conflict=key_hash`, {
                            method: 'POST',
                            headers: {
                                'Content-Type': 'application/json',
                                'apikey': SUPABASE_ANON_KEY,
                                'Authorization': `Bearer ${SUPABASE_ANON_KEY}`,
                                'Prefer': 'resolution=merge-duplicates'
                            },
                            body: JSON.stringify({
                                key_hash: fullKey,
                                data: data,
                                last_updated: data.lastUpdated
                            })
                        });
                        hasUnsavedChanges = false;
                    } catch (err) {
                        console.error("Failed to clear remote database on reset:", err);
                    }
                }
                
                toggleSettings();
                // Force end any active session and return to main page
                if (!document.getElementById('study-screen').classList.contains('hidden')) {
                    if (sessionEndTimeout) { clearTimeout(sessionEndTimeout); sessionEndTimeout = null; }
                    isSessionComplete = true;
                    endSession();
                }
                updateMissedUI();
                updateSetOptions();
                updateDashboard();
        }

        function resetProgressLocal() {
                if (!confirm('Reset all progress locally? Cloud data will remain unchanged.')) return;
                localStorage.removeItem('greLastSeenWords');
                localStorage.removeItem('greMissedWords');
                localStorage.removeItem('greProgressDB');
                localStorage.removeItem('greStreak');
                localStorage.removeItem('greLastStudyDate');
                localStorage.removeItem('greWordsLearnedToday');
                localStorage.removeItem('learned-words');
                localStorage.removeItem('greWordStatuses');
                localStorage.removeItem('greSyncMasteredToLearned');
                missedWordsDB = {};
                progressDB = {};
                if (typeof initGamification === 'function') initGamification();
                
                toggleSettings();
                // Force end any active session and return to main page
                if (!document.getElementById('study-screen').classList.contains('hidden')) {
                    if (sessionEndTimeout) { clearTimeout(sessionEndTimeout); sessionEndTimeout = null; }
                    isSessionComplete = true;
                    endSession();
                }
                updateMissedUI();
                updateSetOptions();
                updateDashboard();
        }

        function initGamification() {
            const today = new Date().toDateString();
            let lastDate = localStorage.getItem('greLastStudyDate');
            let streak = parseInt(localStorage.getItem('greStreak') || '0');
            let wordsToday = parseInt(localStorage.getItem('greWordsLearnedToday') || '0');

            if (lastDate !== today) {
                if (lastDate) {
                    const last = new Date(lastDate);
                    const now = new Date(today);
                    // Set both to midnight to avoid daylight saving time issues
                    last.setHours(0,0,0,0);
                    now.setHours(0,0,0,0);
                    const diffDays = Math.round((now - last) / (1000 * 60 * 60 * 24));
                    
                    if (diffDays > 1) {
                        streak = 0; // Streak broken
                    }
                }
                wordsToday = 0; // New day
                localStorage.setItem('greWordsLearnedToday', 0);
                localStorage.setItem('greStreak', streak);
            }
            updateGamificationUI(streak, wordsToday);
        }

        function incrementGamification(wordObj) {
            const today = new Date().toDateString();
            let lastDate = localStorage.getItem('greLastStudyDate');
            let streak = parseInt(localStorage.getItem('greStreak') || '0');
            let wordsToday = parseInt(localStorage.getItem('greWordsLearnedToday') || '0');

            // Track unique word+type keys practiced today
            let practicedTodayDate = localStorage.getItem('grePracticedTodayDate');
            let practicedTodaySet = new Set();
            if (practicedTodayDate === today) {
                try { practicedTodaySet = new Set(JSON.parse(localStorage.getItem('grePracticedTodayKeys') || '[]')); } catch(e) { practicedTodaySet = new Set(); }
            }
            if (wordObj) {
                practicedTodaySet.add(wordObj.word + '\u0000' + wordObj.type);
            }

            if (lastDate !== today) {
                if (lastDate) {
                    const last = new Date(lastDate);
                    const now = new Date(today);
                    last.setHours(0,0,0,0);
                    now.setHours(0,0,0,0);
                    const diffDays = Math.round((now - last) / (1000 * 60 * 60 * 24));
                    
                    if (diffDays === 1) {
                        streak++;
                    } else if (diffDays > 1) {
                        streak = 1;
                    }
                } else {
                    streak = 1;
                }
                wordsToday = practicedTodaySet.size;
            } else {
                if (streak === 0) streak = 1;
                wordsToday = practicedTodaySet.size;
            }

            localStorage.setItem('greLastStudyDate', today);
            localStorage.setItem('greStreak', streak);
            localStorage.setItem('grePracticedTodayDate', today);
            localStorage.setItem('grePracticedTodayKeys', JSON.stringify(Array.from(practicedTodaySet)));
            localStorage.setItem('greWordsLearnedToday', wordsToday);
            updateGamificationUI(streak, wordsToday);
            hasUnsavedChanges = true;
        }

        function updateGamificationUI(streak, wordsToday) {
            const streakEl = document.getElementById('gamification-streak');
            const wordsEl = document.getElementById('gamification-words');
            if (streakEl) streakEl.innerText = streak;
            if (wordsEl) wordsEl.innerText = wordsToday;
        }

        function addToLastSeen(wordObj, isCorrect) {
            let lastSeen = safeLocalStorageGetJSON('greLastSeenWords', []);
            const idx = getWordIndex(wordObj);
            lastSeen = lastSeen.filter(w => w.idx !== idx);
            const entry = { idx: idx, isCorrect: isCorrect };
            lastSeen.unshift(entry);
            lastSeen = lastSeen.slice(0, 10);
            localStorage.setItem('greLastSeenWords', JSON.stringify(lastSeen));
            incrementGamification(wordObj);
        }

        function updateDashboard() {
            let allWordsSet = new Set();
            let masteredSet = new Set();
            let inReviewSet = new Set();
            let notSeenSet = new Set();
            
            Object.keys(vocabularyDB).forEach(cat => {
                Object.keys(vocabularyDB[cat]).forEach(set => {
                    const setWordsArray = vocabularyDB[cat][set];
                    const setWordsCount = setWordsArray.length;
                    
                    const progressKey = `${cat}|${set}`;
                    const progressVal = progressDB[progressKey];
                    let seenCount = 0;
                    if (progressVal === 'COMPLETED') {
                        seenCount = setWordsCount;
                    } else if (progressVal > 0) {
                        seenCount = parseInt(progressVal);
                    }
                    
                    for(let i=0; i<setWordsCount; i++) {
                        const wordObj = setWordsArray[i];
                        const w = wordObj.word;
                        const wordKey = w + '\u0000' + wordObj.type;
                        
                        allWordsSet.add(wordKey);
                        
                        if (w in missedWordsDB) {
                            inReviewSet.add(wordKey);
                            masteredSet.delete(wordKey);
                            notSeenSet.delete(wordKey);
                        } else {
                            // Check both sequential progress AND the _matched list for non-sequential completions
                            const matchedList = progressDB[progressKey + '_matched'];
                            const isInMatchedList = Array.isArray(matchedList) && matchedList.includes(i);
                            if (i < seenCount || isInMatchedList || progressDB['RM_' + w]) {
                                if (!inReviewSet.has(wordKey)) {
                                    masteredSet.add(wordKey);
                                    notSeenSet.delete(wordKey);
                                }
                            } else {
                                if (!masteredSet.has(wordKey) && !inReviewSet.has(wordKey)) {
                                    notSeenSet.add(wordKey);
                                }
                            }
                        }
                    }
                });
            });

            const dashTotal = document.getElementById('dash-total');
            if (dashTotal) {
                dashTotal.innerText = allWordsSet.size;
                document.getElementById('dash-mastered').innerText = masteredSet.size;
                document.getElementById('dash-review').innerText = inReviewSet.size;
                document.getElementById('dash-notseen').innerText = notSeenSet.size;

                const lastSeenContainer = document.getElementById('dash-last-seen');
                const lastSeenWords = safeLocalStorageGetJSON('greLastSeenWords', []).slice(0, 10);
                
                if (lastSeenWords.length === 0) {
                    lastSeenContainer.innerHTML = '<span class="text-xs text-slate-400 italic">No words seen yet.</span>';
                } else {
                    lastSeenContainer.innerHTML = lastSeenWords.map(entry => {
                        const w = getWordByIndex(entry.idx);
                        const def = (w && w.def) ? w.def.replace(/"/g, '&quot;') : 'No definition available';
                        const wordStr = (w && w.word) ? w.word : '???';
                        let colorClasses = "bg-white dark:bg-neutral-900 border-slate-200 dark:border-neutral-700 text-slate-600 dark:text-slate-300";
                        if (entry.isCorrect === true) {
                            colorClasses = "bg-emerald-50 dark:bg-emerald-900/20 border-emerald-200 dark:border-emerald-800/30 text-emerald-700 dark:text-emerald-400";
                        } else if (entry.isCorrect === false) {
                            colorClasses = "bg-rose-50 dark:bg-rose-900/20 border-rose-200 dark:border-rose-800/30 text-rose-700 dark:text-rose-400";
                        }
                        
                        return `
                            <div class="group relative inline-block" tabindex="0" onmouseenter="positionTooltip(this)">
                                <span class="px-2 py-1 border rounded-md text-xs font-medium shadow-sm cursor-help block transition-colors ${colorClasses}">${wordStr}</span>
                                <div class="dyn-tooltip pointer-events-none absolute bottom-[calc(100%+4px)] left-0 w-max max-w-[200px] sm:max-w-xs opacity-0 transition-opacity duration-150 group-hover:opacity-100 group-focus:opacity-100 bg-slate-800 dark:bg-neutral-800 text-slate-100 text-xs rounded-lg py-2 px-3 z-50 shadow-xl border border-slate-700 dark:border-neutral-700 text-center whitespace-normal">
                                    ${def}
                                    <div class="dyn-arrow absolute top-full left-4 -mt-px border-4 border-transparent border-t-slate-800 dark:border-t-slate-700"></div>
                                </div>
                            </div>
                        `;
                    }).join('');
                }
            }

            const container = document.getElementById('set-progression-container');
            if (container) {
                let html = '';
                Object.keys(vocabularyDB).forEach(cat => {
                    if (cat === 'Random') return;
                    const sets = Object.keys(vocabularyDB[cat]);
                    const isNumbered = sets.every(s => /^Set \d+$/i.test(s));
                    if (isNumbered) sets.sort((a, b) => a.localeCompare(b, undefined, {numeric: true, sensitivity: 'base'}));

                    let totalWords = 0, totalDone = 0, setsCompleted = 0;
                    sets.forEach(set => {
                        const words = vocabularyDB[cat][set];
                        const count = words.length;
                        totalWords += count;
                        const progressKey = cat + '|' + set;
                        const progressVal = progressDB[progressKey];
                        let done = 0;
                        if (progressVal === 'COMPLETED') {
                            done = count;
                            setsCompleted++;
                        } else if (progressVal > 0) {
                            done = parseInt(progressVal) || 0;
                        }
                        const matchedList = progressDB[progressKey + '_matched'];
                        if (Array.isArray(matchedList)) {
                            const matchedCount = matchedList.filter(idx => idx >= done).length;
                            done = Math.min(done + matchedCount, count);
                        }
                        totalDone += done;
                    });

                    const pct = totalWords > 0 ? Math.round(totalDone / totalWords * 100) : 0;


                    html += `<div class="dash-cat-card bg-slate-50 dark:bg-neutral-800/50 border border-slate-200 dark:border-neutral-700 rounded-xl px-3 py-2.5" onclick="window._selectDashCategory('${cat.replace(/'/g,"\\'")}')">
                        <div class="flex items-center justify-between mb-1">
                            <span class="text-[10px] sm:text-[11px] font-bold text-slate-700 dark:text-slate-200 uppercase tracking-wider truncate">${cat}</span>
                            <span class="text-[9px] sm:text-[10px] font-bold text-primary-600 dark:text-primary-400 ml-1 shrink-0">${pct}%</span>
                        </div>
                        <div class="text-[9px] sm:text-[10px] font-medium text-slate-500 dark:text-slate-400">
                            <span class="text-primary-600 dark:text-primary-400 font-semibold">${setsCompleted}</span>/<span class="font-semibold">${sets.length}</span> sets completed
                        </div>
                    </div>`;
                });
                container.innerHTML = html;
            }
        }

        function _selectDashCategory(cat) {
            catSelect.value = cat;
            localStorage.setItem('greLastCategory', cat);
            updateSetOptions(true);
            showSetup();
        }

        function positionTooltip(el) {
            const tooltip = el.querySelector('.dyn-tooltip');
            const arrow = el.querySelector('.dyn-arrow');
            if (!tooltip || !arrow) return;
            
            const rect = el.getBoundingClientRect();
            if (rect.right > window.innerWidth / 2) {
                tooltip.classList.remove('left-0');
                tooltip.classList.add('right-0');
                arrow.classList.remove('left-1.5', 'left-4');
                arrow.classList.add('right-4');
            } else {
                tooltip.classList.remove('right-0');
                tooltip.classList.add('left-0');
                arrow.classList.remove('right-4');
                if (el.innerHTML.includes('M13 16h-1')) {
                    arrow.classList.add('left-1.5');
                } else {
                    arrow.classList.add('left-4');
                }
            }
        }

        // =========================================================
        // 4. MENU SETUP
        // =========================================================
        const catSelect = document.getElementById('category-select');
        const setSelect = document.getElementById('set-select');
        const launchBtn = document.getElementById('launch-btn');
        const setPrevBtn = document.getElementById('set-prev-btn');
        const setNextBtn = document.getElementById('set-next-btn');
        let currentSetsList = [];

        function initSetupMenus() {
            updateDashboard();
            const populatedCategories = Object.keys(vocabularyDB).filter(cat => Object.keys(vocabularyDB[cat]).length > 0);
            
            if (populatedCategories.length > 0) {
                populatedCategories.push("Random");
                catSelect.innerHTML = populatedCategories.map(c => `<option value="${c}">${c}</option>`).join('');
                
                const savedCat = localStorage.getItem('greLastCategory');
                if (savedCat && populatedCategories.includes(savedCat)) {
                    catSelect.value = savedCat;
                }

                launchBtn.disabled = false;
                updateSetOptions();
                toggleCategory(true);
            } else {
                catSelect.innerHTML = `<option value="" disabled selected>No database.js found. Read setup guide.</option>`;
                setSelect.innerHTML = '';
                launchBtn.disabled = true;
                launchBtn.innerText = "Waiting for data...";
            }
            // Restore saved study mode
            const savedMode = localStorage.getItem('greStudyMode');
            if (savedMode) {
                const radio = document.querySelector(`input[name="mode"][value="${savedMode}"]`);
                if (radio) {
                    radio.checked = true;
                }
            }
            if (typeof onStudyModeChange === 'function') {
                onStudyModeChange();
            }
            updateMissedUI();
        }

        // Global function to toggle Category and Set selector visibility on study mode changes
        window.onStudyModeChange = function() {
            const selectedModeEl = document.querySelector('input[name="mode"]:checked');
            const selectedMode = selectedModeEl ? selectedModeEl.value : 'mcq';
            const catContainer = document.getElementById('category-container');
            const setProgressContainer = document.getElementById('set-progress-container');
            const launchBtn = document.getElementById('launch-btn');
            
            if (catContainer) catContainer.classList.remove('hidden');
            if (setProgressContainer) setProgressContainer.classList.remove('hidden');
            updateSetOptions();
            if (launchBtn) {
                launchBtn.innerText = "Begin";
            }
        };

        function updateSetOptions(isCategoryChange = false) {
            const cat = catSelect.value;
            if (!cat) return;
            localStorage.setItem('greLastCategory', cat);
            
            if (cat === 'Random') {
                setSelect.innerHTML = `<option value="Random">No effect on progress</option>`;
                setSelect.disabled = true;
                currentSetsList = [];
                if (setPrevBtn) setPrevBtn.disabled = true;
                if (setNextBtn) setNextBtn.disabled = true;
                document.getElementById('category-summary-text').innerText = `Random Practice`;
                const container = document.getElementById('set-progress-container');
                if (container) {
                    container.classList.add('opacity-0');
                    setTimeout(() => container.classList.add('hidden'), 300);
                }
                document.getElementById('launch-btn').innerText = "Begin";
                return;
            } else {
                setSelect.disabled = false;
            }

            const sets = Object.keys(vocabularyDB[cat] || {});
            // Categories like GRE-Frequent/Remaining/Extra store sets as "Set 1", "Set 2", ...
            // but object key order for those isn't numeric (e.g. "Set 1", "Set 10", "Set 11", ...
            // "Set 2"), so they need a numeric sort to display correctly. Other categories
            // (like GRE-Selected, with custom-named sets such as "Basic 1", "Core", "Top")
            // are deliberately ordered in the database file itself, so leave those as-is.
            const isNumberedSetList = sets.every(s => /^Set \d+$/i.test(s));
            if (isNumberedSetList) {
                sets.sort((a, b) => a.localeCompare(b, undefined, {numeric: true, sensitivity: 'base'}));
            }
            currentSetsList = sets;
            
            setSelect.innerHTML = sets.map(s => {
                const progressKey = `${cat}|${s}`;
                const progressVal = progressDB[progressKey];
                
                let optionText = s;
                let optionStyle = ''; 
                let extraClass = '';

                if (progressVal === 'COMPLETED') {
                    optionText = `${s} (Completed)`;
                    optionStyle = 'color: #94a3b8;';
                    extraClass = 'text-slate-400 dark:text-slate-500';
                }

                return `<option value="${s}" style="${optionStyle}" class="${extraClass}">${optionText}</option>`;
            }).join('');
            
            if (isCategoryChange) {
                // Auto-select the latest touched set: the last non-completed set
                // that has any progress (sequential or matched). Skip completed
                // sets. If no set has progress, default to Set 1 (first set).
                let targetSet = sets[0];
                for (const s of sets) {
                    const progressKey = `${cat}|${s}`;
                    const progressVal = progressDB[progressKey];
                    if (progressVal === 'COMPLETED') continue;
                    const matchedList = progressDB[progressKey + '_matched'];
                    const hasProgress = (typeof progressVal === 'number' && progressVal > 0) ||
                                        (Array.isArray(matchedList) && matchedList.length > 0);
                    if (hasProgress) {
                        targetSet = s;
                    }
                }
                setSelect.value = targetSet;
                localStorage.setItem('greLastSet', targetSet);
            } else {
                const savedSet = localStorage.getItem('greLastSet');
                if (savedSet && sets.includes(savedSet)) {
                    setSelect.value = savedSet;
                }
            }
            
            document.getElementById('category-summary-text').innerText = `${cat} / ${setSelect.value}`;
            updateSetNavButtons();
            updateSetProgressUI();
        }

        function updateSetNavButtons() {
            if (!setPrevBtn || !setNextBtn) return;
            const idx = currentSetsList.indexOf(setSelect.value);
            if (idx === -1) {
                setPrevBtn.disabled = true;
                setNextBtn.disabled = true;
                return;
            }
            // Cycle through sets instead of graying out at the first/last set —
            // only disable when there's nothing to cycle through at all.
            setPrevBtn.disabled = currentSetsList.length <= 1;
            setNextBtn.disabled = currentSetsList.length <= 1;
        }

        function navigateSet(direction) {
            const idx = currentSetsList.indexOf(setSelect.value);
            if (idx === -1) return;
            if (currentSetsList.length <= 1) return;
            const newIdx = (idx + direction + currentSetsList.length) % currentSetsList.length;

            setSelect.value = currentSetsList[newIdx];
            localStorage.setItem('greLastSet', setSelect.value);
            document.getElementById('category-summary-text').innerText = `${catSelect.value} / ${setSelect.value}`;
            updateSetNavButtons();
            updateSetProgressUI();
        }

        function updateSetProgressUI() {
            const cat = catSelect.value;
            const set = setSelect.value;
            if(!cat || !set) return;

            const container = document.getElementById('set-progress-container');
            const total = vocabularyDB[cat][set].length;
            const progressKey = `${cat}|${set}`;
            const progressVal = progressDB[progressKey];

            let pct = 0;
            let current = 0;

            if (progressVal === 'COMPLETED') {
                pct = 100;
                current = total;
            } else {
                const matchedArr = progressDB[progressKey + '_matched'];
                if (Array.isArray(matchedArr)) {
                    current = matchedArr.length;
                } else if (progressVal !== undefined) {
                    current = parseInt(progressVal) || 0;
                }
                
                if (current > 0) {
                    pct = Math.round((current / total) * 100);
                    if (pct === 0 && current > 0) pct = 1;
                    if (pct === 100 && current < total) pct = 99;
                }
            }

            container.classList.remove('hidden');
            // Allow display:block to apply before changing opacity for transition
            setTimeout(() => container.classList.remove('opacity-0'), 10);

            // Brief flash so the user notices the numbers updated, even when
            // switching between two sets that happen to show the same values
            // (e.g. 0/30 -> 0/30).
            container.classList.remove('progress-flash');
            void container.offsetWidth; // force reflow to restart the animation
            container.classList.add('progress-flash');

            document.getElementById('set-progress-pct').innerText = `${pct}%`;
            document.getElementById('set-progress-fill').style.width = `${pct}%`;
            
            const launchBtn = document.getElementById('launch-btn');
            if (current > 0 && progressVal !== 'COMPLETED') {
                launchBtn.innerText = "Continue";
            } else {
                launchBtn.innerText = "Begin";
            }
            
            if (progressVal === 'COMPLETED') {
                document.getElementById('set-progress-fill').classList.remove('bg-primary-500');
                document.getElementById('set-progress-fill').classList.add('bg-emerald-500');
                document.getElementById('set-progress-pct').classList.remove('text-primary-600', 'dark:text-primary-400', 'bg-primary-50', 'dark:bg-primary-900/40');
                document.getElementById('set-progress-pct').classList.add('text-emerald-600', 'dark:text-emerald-400', 'bg-emerald-50', 'dark:bg-emerald-900/40');
                document.getElementById('set-progress-status').innerText = `✓ Set complete`;
            } else {
                document.getElementById('set-progress-fill').classList.add('bg-primary-500');
                document.getElementById('set-progress-fill').classList.remove('bg-emerald-500');
                document.getElementById('set-progress-pct').classList.add('text-primary-600', 'dark:text-primary-400', 'bg-primary-50', 'dark:bg-primary-900/40');
                document.getElementById('set-progress-pct').classList.remove('text-emerald-600', 'dark:text-emerald-400', 'bg-emerald-50', 'dark:bg-emerald-900/40');
                document.getElementById('set-progress-status').innerText = `${current} / ${total} words completed`;
            }
        }

        catSelect.addEventListener('change', () => {
            updateSetOptions(true);
            const details = document.getElementById('category-details');
            const chevron = document.getElementById('category-chevron');
            const studyModeContainer = document.getElementById('study-mode-container');
            const launchBtn = document.getElementById('launch-btn');
            if (details.classList.contains('hidden')) {
                details.classList.remove('hidden');
                chevron.classList.add('rotate-180');
                if (studyModeContainer) studyModeContainer.classList.add('compact-modes');
                if (launchBtn) launchBtn.classList.add('compact-modes');
                details.classList.remove('fade-in');
                requestAnimationFrame(() => {
                    details.classList.add('fade-in');
                });
            } else {
                details.classList.remove('fade-in');
                requestAnimationFrame(() => {
                    details.classList.add('fade-in');
                });
            }
            setSelect.classList.remove('ring-2', 'ring-primary-500');
            requestAnimationFrame(() => {
                setSelect.classList.add('ring-2', 'ring-primary-500');
                setTimeout(() => setSelect.classList.remove('ring-2', 'ring-primary-500'), 1000);
            });
        });
        setSelect.addEventListener('change', () => {
            localStorage.setItem('greLastSet', setSelect.value);
            document.getElementById('category-summary-text').innerText = `${catSelect.value} / ${setSelect.value}`;
            updateSetNavButtons();
            updateSetProgressUI();
        });
        initSetupMenus(); 
        initSettings(); 
        initGamification();

        // =========================================================
        // FLASHCARD GESTURE (SWIPE / TOSS) CONTROLLER
        // =========================================================
        function initFlashcardGestures() {
            const flashcard = document.getElementById('flashcard');
            if (!flashcard) return;

            flashcard.addEventListener('pointerdown', (e) => {
                if (mode !== 'flashcard' || isSessionComplete) return;
                
                // Only allow dragging/swiping when the card is flipped (definition is displayed)
                if (!isFlipped) return;
                
                // Avoid dragging on button or voice icon taps
                if (e.target.closest('button') || e.target.closest('a')) return;
                
                preventNextFlip = false; // Reset flip prevention for new gesture
                startX = e.clientX;
                startY = e.clientY;
                startTime = Date.now();
                isDraggingCard = true;
                
                flashcard.setPointerCapture(e.pointerId);
                flashcard.style.transition = 'none';
                flashcard.style.touchAction = 'none'; // Lock scrolling during active swipe drag
            });

            flashcard.addEventListener('pointermove', (e) => {
                if (!isDraggingCard) return;
                
                const deltaX = e.clientX - startX;
                const deltaY = e.clientY - startY;
                
                // Determine if we crossed the threshold to distinguish drag from tap
                if (Math.abs(deltaX) > dragThreshold || Math.abs(deltaY) > dragThreshold) {
                    preventNextFlip = true;
                }
                
                if (preventNextFlip) {
                    const disclaimer = document.getElementById('swipe-disclaimer');
                    if (disclaimer) disclaimer.classList.add('hidden');
                    
                    let rotation = deltaX * rotationFactor;
                    
                    // Render translation & rotation
                    if (isFlipped) {
                        flashcard.style.transform = `translate3d(${deltaX}px, ${deltaY}px, 0) rotate(${-rotation}deg) rotateY(180deg)`;
                    } else {
                        flashcard.style.transform = `translate3d(${deltaX}px, ${deltaY}px, 0) rotate(${rotation}deg)`;
                    }
                    
                    // Update visual stamps (Review / Knew It) opacity
                    const leftOverlays = document.querySelectorAll('.swipe-overlay-left');
                    const rightOverlays = document.querySelectorAll('.swipe-overlay-right');
                    
                    const progress = Math.min(Math.abs(deltaX) / maxGlowDistance, 1);
                    const opacity = Math.pow(progress, 0.7); // Rises faster at the start so the glow triggers immediately and smoothly
                    
                    if (deltaX < 0) {
                        leftOverlays.forEach(el => el.style.opacity = opacity);
                        rightOverlays.forEach(el => el.style.opacity = 0);
                    } else {
                        rightOverlays.forEach(el => el.style.opacity = opacity);
                        leftOverlays.forEach(el => el.style.opacity = 0);
                    }
                }
            });

            flashcard.addEventListener('pointerup', (e) => {
                if (!isDraggingCard) return;
                isDraggingCard = false;
                
                try {
                    flashcard.releasePointerCapture(e.pointerId);
                } catch (err) {}
                
                const deltaX = e.clientX - startX;
                const elapsedTime = Date.now() - startTime;
                const velocityX = deltaX / (elapsedTime || 1); // Avoid division by zero
                const isFlick = Math.abs(velocityX) > 0.55 && Math.abs(deltaX) > 50; // Flick detection (speed > 0.55px/ms & distance > 50px)
                
                // Add smooth transition for reset or flyaway animation
                const randomDuration = 0.12 + Math.random() * 0.08; // 120ms to 200ms
                flashcard.style.transition = `transform ${randomDuration}s cubic-bezier(0.1, 0.8, 0.3, 1), opacity ${randomDuration}s ease`;
                
                if (preventNextFlip && (Math.abs(deltaX) > tossThreshold || isFlick)) {
                    // Toss action!
                    justTossed = true;
                    const knewIt = deltaX > 0;
                    const targetX = knewIt ? 1000 : -1000;
                    const randomAngle = 55 + Math.random() * 30; // Random tilt between 55 and 85 degrees
                    const targetRotation = knewIt ? randomAngle : -randomAngle;
                    const targetY = (Math.random() - 0.5) * 160; // Random vertical variation (-80px to +80px)
                    
                    if (isFlipped) {
                        flashcard.style.transform = `translate3d(${targetX}px, ${targetY}px, 0) rotate(${-targetRotation}deg) rotateY(180deg)`;
                    } else {
                        flashcard.style.transform = `translate3d(${targetX}px, ${targetY}px, 0) rotate(${targetRotation}deg)`;
                    }
                    flashcard.style.opacity = '0';
                    
                    // Keep the winning stamp fully visible during toss
                    const leftOverlays = document.querySelectorAll('.swipe-overlay-left');
                    const rightOverlays = document.querySelectorAll('.swipe-overlay-right');
                    if (knewIt) {
                        rightOverlays.forEach(el => el.style.opacity = 1);
                        leftOverlays.forEach(el => el.style.opacity = 0);
                    } else {
                        leftOverlays.forEach(el => el.style.opacity = 1);
                        rightOverlays.forEach(el => el.style.opacity = 0);
                    }
                    
                    const durationMs = Math.round(randomDuration * 1000);
                    setTimeout(() => {
                        processSelfRating(knewIt);
                        
                        // Reset card state (will render the new card word)
                        flashcard.style.transition = 'none';
                        flashcard.style.transform = ''; // Clear inline transform so stylesheet CSS can govern flip states
                        flashcard.style.opacity = '1';
                        // Since next card starts unflipped, lock scroll
                        flashcard.style.touchAction = 'none';
                        
                        document.querySelectorAll('.swipe-overlay').forEach(el => {
                            el.style.transition = 'none';
                            el.style.opacity = 0;
                        });
                        
                        setTimeout(() => {
                            flashcard.style.transition = '';
                            preventNextFlip = false;
                            justTossed = false;
                            document.querySelectorAll('.swipe-overlay').forEach(el => {
                                el.style.transition = '';
                            });
                        }, 100);
                    }, durationMs);
                } else {
                    // Snap back to center
                    flashcard.style.transform = ''; // Clear inline transform so stylesheet CSS can govern flip states
                    
                    const disclaimer = document.getElementById('swipe-disclaimer');
                    if (disclaimer) disclaimer.classList.remove('hidden');
                    
                    document.querySelectorAll('.swipe-overlay').forEach(el => {
                        el.style.transition = 'opacity 0.2s ease';
                        el.style.opacity = 0;
                        setTimeout(() => {
                            el.style.transition = '';
                        }, 200);
                    });
                    
                    // Reset flip prevention much faster so subsequent taps respond immediately
                    setTimeout(() => {
                        flashcard.style.transition = '';
                        preventNextFlip = false;
                        flashcard.style.touchAction = 'none';
                    }, 100);
                }
            });

            flashcard.addEventListener('pointercancel', (e) => {
                if (!isDraggingCard) return;
                isDraggingCard = false;
                try {
                    flashcard.releasePointerCapture(e.pointerId);
                } catch (err) {}
                
                flashcard.style.transition = 'transform 0.15s cubic-bezier(0.1, 0.8, 0.3, 1)';
                flashcard.style.transform = ''; // Clear inline transform so stylesheet CSS can govern flip states
                
                const disclaimer = document.getElementById('swipe-disclaimer');
                if (disclaimer) disclaimer.classList.remove('hidden');
                
                document.querySelectorAll('.swipe-overlay').forEach(el => {
                    el.style.opacity = 0;
                });
                
                // Reset flip prevention much faster so subsequent taps respond immediately
                setTimeout(() => {
                    flashcard.style.transition = '';
                    preventNextFlip = false;
                    flashcard.style.touchAction = 'none';
                }, 100);
            });
        }
        initFlashcardGestures();

        function updateMissedUI() {
            const arr = Object.values(missedWordsDB);
            const btn = document.getElementById('review-btn');
            document.getElementById('missed-count').innerText = arr.length;
            if(arr.length > 0) {
                btn.classList.remove('hidden');
                btn.classList.add('flex');
            } else {
                btn.classList.add('hidden');
                btn.classList.remove('flex');
            }
        }

        function toggleCategory(forceCollapse = false) {
            const details = document.getElementById('category-details');
            const chevron = document.getElementById('category-chevron');
            const studyModeContainer = document.getElementById('study-mode-container');
            const launchBtn = document.getElementById('launch-btn');
            
            if (forceCollapse || !details.classList.contains('hidden')) {
                details.classList.add('hidden');
                chevron.classList.remove('rotate-180');
                if (studyModeContainer) studyModeContainer.classList.remove('compact-modes');
                if (launchBtn) launchBtn.classList.remove('compact-modes');
            } else {
                details.classList.remove('hidden');
                chevron.classList.add('rotate-180');
                if (studyModeContainer) studyModeContainer.classList.add('compact-modes');
                if (launchBtn) launchBtn.classList.add('compact-modes');
            }
        }

        // =========================================================
        // 5. SESSION LAUNCH & LOGIC
        // =========================================================
        function startStandardSession() {
            const selectedStudyMode = document.querySelector('input[name="mode"]:checked').value;

            const cat = catSelect.value;
            const set = setSelect.value;
            if(!cat || !set) return;
            
            if (cat === 'Random') {
                let allWords = [];
                const seenWords = new Set();
                Object.keys(vocabularyDB).forEach(c => {
                    Object.keys(vocabularyDB[c]).forEach(s => {
                        vocabularyDB[c][s].forEach(w => {
                            // De-dupe by word text in case the same word appears in
                            // more than one category/set, so appData never contains
                            // two entries with the same word text.
                            if (!seenWords.has(w.word)) {
                                seenWords.add(w.word);
                                allWords.push(w);
                            }
                        });
                    });
                });
                
                if (allWords.length === 0) return;
                
                // Sample WITHOUT replacement. Drag Match identifies a word's slot in
                // appData via indexOf/findIndex on word text, which always resolves
                // to the first match — duplicate words in the same session broke that.
                const shuffled = allWords.sort(() => 0.5 - Math.random());
                appData = shuffled.slice(0, Math.min(25, shuffled.length));
                isReviewMode = false;
                fillBlanksOrder = null;
                document.getElementById('session-title').innerText = `Random Practice`;
                launchCoreSession();
                return;
            }

            const progressKey = `${cat}|${set}`;
            if (progressDB[progressKey] === 'COMPLETED') {
                if(!confirm("You've already completed this set. Are you sure you want to study it again?")) {
                    return;
                }
                progressDB[progressKey] = 0;
                delete progressDB[progressKey + '_matched'];
                localStorage.setItem('greProgressDB', JSON.stringify(progressDB));
                updateSetOptions(); 
            }

            appData = [...vocabularyDB[cat][set]]; 
            // Fill in the Blanks: build a shuffled presentation order so words
            // are shown in random sequence but appData indices stay stable for
            // progress tracking (sessionMatchedIndices).
            if (selectedStudyMode === 'fillblanks') {
                fillBlanksOrder = Array.from({length: appData.length}, (_, i) => i).sort(() => 0.5 - Math.random());
            } else {
                fillBlanksOrder = null;
            }
            isReviewMode = false;
            document.getElementById('session-title').innerText = `${cat} / ${set}`;
            launchCoreSession();
        }

        function startReviewSession() {
            appData = Object.values(missedWordsDB)
                .map(idx => getWordByIndex(idx))
                .filter(Boolean)
                .sort(() => 0.5 - Math.random());
            if (appData.length === 0) return;
            
            isReviewMode = true;
            document.getElementById('session-title').innerText = "Reviewing Missed Words";

            // Set fillBlanksOrder for the current mode and appData so a stale
            // array from a previous fill-blanks session doesn't cause early exit.
            const selectedMode = document.querySelector('input[name="mode"]:checked').value;
            if (selectedMode === 'fillblanks') {
                fillBlanksOrder = Array.from({length: appData.length}, (_, i) => i).sort(() => 0.5 - Math.random());
            } else {
                fillBlanksOrder = null;
            }

            launchCoreSession();
        }

        function launchCoreSession() {
            _navStack.push('study-screen');
            mode = document.querySelector('input[name="mode"]:checked').value;
            localStorage.setItem('greStudyMode', mode);

            // Cancel any pending auto-end timeout from a previous session
            if (sessionEndTimeout) { clearTimeout(sessionEndTimeout); sessionEndTimeout = null; }

            if (!isReviewMode) {
                const progressKey = `${catSelect.value}|${setSelect.value}`;
                currentIndex = parseInt(progressDB[progressKey]) || 0;
                
                if (typeof sessionMatchedIndices !== 'undefined') {
                    sessionMatchedIndices.clear();
                    const savedMatched = progressDB[progressKey + '_matched'];
                    if (Array.isArray(savedMatched)) {
                        sessionMatchedIndices = new Set(savedMatched);
                    } else {
                        // Populate based on sequential index if no matched list exists
                        for (let i = 0; i < currentIndex; i++) {
                            sessionMatchedIndices.add(i);
                        }
                    }
                    
                    // Re-calculate the first unmatched index to start cleanly from
                    if (fillBlanksOrder) {
                        // For fill-blanks, find the first unmatched entry in the shuffled order
                        fillBlanksPointer = 0;
                        while (fillBlanksPointer < fillBlanksOrder.length && sessionMatchedIndices.has(fillBlanksOrder[fillBlanksPointer])) {
                            fillBlanksPointer++;
                        }
                        currentIndex = fillBlanksPointer < fillBlanksOrder.length ? fillBlanksOrder[fillBlanksPointer] : 0;
                    } else {
                        let startIdx = 0;
                        while (startIdx < appData.length && sessionMatchedIndices.has(startIdx)) {
                            startIdx++;
                        }
                        currentIndex = startIdx;
                    }
                }
            } else {
                currentIndex = 0;
                fillBlanksPointer = 0;
                if (typeof sessionMatchedIndices !== 'undefined') {
                    sessionMatchedIndices.clear();
                }
            }

            isSessionComplete = false;
            isCardCollapsed = false;
            reviewCorrectCount = 0;
            _hideAllContentScreens();
            document.getElementById('study-screen').classList.remove('hidden');
            document.getElementById('study-screen').classList.add('flex');
            document.getElementById('end-session-btn').classList.remove('hidden');
            document.getElementById('nav-branding').classList.add('hidden');
            
            document.body.classList.add('overflow-hidden');
            document.body.style.touchAction = 'none';
            document.querySelector('main').style.paddingTop = '0.5rem';
            
            document.getElementById('card-container').classList.add('cursor-pointer');
            renderCard();
        }

        function endSession() {
            if (sessionEndTimeout) { clearTimeout(sessionEndTimeout); sessionEndTimeout = null; }
            if (document.getElementById('study-screen').classList.contains('hidden')) return;
            if ('speechSynthesis' in window) window.speechSynthesis.cancel();

            if(isSessionComplete || confirm("Exit the current study session? Progress is saved locally.")) {
                // Restore page scroll and key handler
                const mainEl = document.querySelector('main');
                if (mainEl) { mainEl.style.overflow = ''; mainEl.style.overflowY = ''; }
                document.body.style.overflow = '';

                updateDashboard();
                document.getElementById('matching-container').classList.add('hidden');

                toggleCategory(true);
                showSetup();
                pushToCloud();
            }
        }

        function updateSessionProgress() {
            const progressText = document.getElementById('session-progress-text');
            const progressBar = document.getElementById('progress-bar');
            if (!progressText || !progressBar) return;

            const completed = typeof sessionMatchedIndices !== 'undefined' ? sessionMatchedIndices.size : 0;

            if (mode === 'matching') {
                progressText.innerText = `Completed ${completed} of ${appData.length} words`;
                const pct = appData.length > 0 ? (completed / appData.length) * 100 : 0;
                progressBar.style.width = `${pct}%`;

            } else if (isReviewMode) {
                const wordNum = Math.min(reviewCorrectCount + 1, appData.length);
                progressText.innerText = `Word ${wordNum} of ${appData.length}`;
                const pct = appData.length > 0 ? (reviewCorrectCount / appData.length) * 100 : 0;
                progressBar.style.width = `${pct}%`;
            } else {
                const wordNum = Math.min(completed + 1, appData.length);
                progressText.innerText = `Word ${wordNum} of ${appData.length}`;
                const pct = appData.length > 0 ? (completed / appData.length) * 100 : 0;
                progressBar.style.width = `${pct}%`;
            }
        }
        function completeWord(idx) {
            if (isReviewMode) return;
            
            sessionMatchedIndices.add(idx);
            
            if (catSelect.value !== 'Random') {
                const progressKey = `${catSelect.value}|${setSelect.value}`;
                progressDB[progressKey + '_matched'] = Array.from(sessionMatchedIndices);
                
                // Re-calculate the first unmatched index to see what to set progressDB[progressKey] to
                let startIdx = 0;
                while (startIdx < appData.length && sessionMatchedIndices.has(startIdx)) {
                    startIdx++;
                }
                
                if (startIdx >= appData.length) {
                    progressDB[progressKey] = 'COMPLETED';
                    delete progressDB[progressKey + '_matched'];
                } else {
                    progressDB[progressKey] = startIdx;
                }
                
                // Sync progress for this word to all other sets/categories
                if (appData[idx] && appData[idx].word) {
                    const cleanWord = appData[idx].word.trim().toLowerCase();
                    const targetType = appData[idx].type ? appData[idx].type.trim().toLowerCase() : '';
                    
                    Object.keys(vocabularyDB).forEach(otherCat => {
                        Object.keys(vocabularyDB[otherCat]).forEach(otherSet => {
                            if (otherCat === catSelect.value && otherSet === setSelect.value) return;
                            
                            const otherWords = vocabularyDB[otherCat][otherSet];
                            otherWords.forEach((w, otherIdx) => {
                                // Match both word spelling and part of speech (crucial for steep adj. vs steep verb)
                                const otherWordClean = w.word.trim().toLowerCase();
                                const otherTypeClean = w.type ? w.type.trim().toLowerCase() : '';
                                
                                if (otherWordClean === cleanWord && otherTypeClean === targetType) {
                                    const otherProgressKey = `${otherCat}|${otherSet}`;
                                    
                                    // Expand existing matched list or create new
                                    let otherMatched = progressDB[otherProgressKey + '_matched'];
                                    if (!Array.isArray(otherMatched)) {
                                        const currentVal = progressDB[otherProgressKey];
                                        otherMatched = [];
                                        if (currentVal === 'COMPLETED') {
                                            for (let i = 0; i < otherWords.length; i++) otherMatched.push(i);
                                        } else {
                                            const limit = parseInt(currentVal) || 0;
                                            for (let i = 0; i < limit; i++) otherMatched.push(i);
                                        }
                                    }
                                    
                                    if (!otherMatched.includes(otherIdx)) {
                                        otherMatched.push(otherIdx);
                                        progressDB[otherProgressKey + '_matched'] = otherMatched;
                                        
                                        // Re-calculate
                                        let sIdx = 0;
                                        while (sIdx < otherWords.length && otherMatched.includes(sIdx)) {
                                            sIdx++;
                                        }
                                        if (sIdx >= otherWords.length) {
                                            progressDB[otherProgressKey] = 'COMPLETED';
                                            delete progressDB[otherProgressKey + '_matched'];
                                        } else {
                                            progressDB[otherProgressKey] = sIdx;
                                        }
                                    }
                                }
                            });
                        });
                    });
                }
                
                localStorage.setItem('greProgressDB', JSON.stringify(progressDB));
                hasUnsavedChanges = true;
            }
        }

        function renderCard() {

            isFlipped = false;
            isAnswered = false;
            hasAutoPronouncedThisCard = false;
            const flashcard = document.getElementById('flashcard');
            flashcard.classList.remove('flipped');
            flashcard.style.touchAction = 'none'; // non-scrollable before flipped
            
            if (mode === 'fillblanks') {
                flashcard.classList.remove('cursor-pointer');
                flashcard.classList.add('cursor-default');
            } else {
                flashcard.classList.add('cursor-pointer');
                flashcard.classList.remove('cursor-default');
            }
            
            const disclaimer = document.getElementById('swipe-disclaimer');
            if (disclaimer) disclaimer.classList.add('hidden');
            
            const wordObj = appData[currentIndex];
            const frontText = document.getElementById('card-front-word');
            frontText.classList.remove('hidden', 'text-emerald-600', 'dark:text-emerald-400', 'normal-case');
            frontText.classList.add('text-slate-800', 'dark:text-white');
            document.getElementById('card-front-fillblanks').classList.add('hidden');
            document.getElementById('card-front-fillblanks').classList.remove('flex');
            const typeEl = document.getElementById('card-front-type');
            if (mode === 'flashcard') {
                document.getElementById('card-front-word').innerText = wordObj.word;
                if (typeEl) {
                    typeEl.innerText = `${wordObj.type}`;
                    typeEl.classList.remove('hidden');
                }
            } else {
                document.getElementById('card-front-word').innerText = wordObj.word;
                if (typeEl) {
                    typeEl.classList.add('hidden');
                }
            }
            document.getElementById('card-back-word').innerText = wordObj.word;
            
            applyWordCase();
            document.getElementById('card-back-type').innerText = wordObj.type;
            document.getElementById('card-back-def').innerText = wordObj.def;

            // Apply current collapse state
            if (mode === 'mcq') {
                const autoShow = localStorage.getItem('greAutoShowSentences') === 'true';
                isCardCollapsed = !autoShow;
            } else {
                isCardCollapsed = false;
            }
            const container = document.getElementById('card-container');
            const btns = [document.getElementById('example-btn-front'), document.getElementById('example-btn-back')];
            if (isCardCollapsed) {
                container.classList.add('card-collapsed');
                btns.forEach(btn => {
                    if (btn) btn.title = "Expand Card";
                });
            } else {
                container.classList.remove('card-collapsed');
                btns.forEach(btn => {
                    if (btn) {
                        if (mode === 'mcq') {
                            btn.title = "Collapse Card";
                        } else {
                            btn.title = "Show Example";
                        }
                    }
                });
            }

            updateSessionProgress();

            // FIX: Set wrapper to invisible initially instead of display: none
            hideNavControls();

            document.getElementById('flashcard-rating-controls').classList.add('hidden');
            document.getElementById('next-btn').disabled = true;
            if (mode === 'mcq' || mode === 'matching' || mode === 'fillblanks') {
                document.getElementById('next-btn-container').classList.remove('hidden');
            } else {
                document.getElementById('next-btn-container').classList.add('hidden');
            }
            
            // Ensure pronounce buttons are visible for normal cards
            document.getElementById('pronounce-btn-front').classList.remove('hidden');
            document.getElementById('pronounce-btn-back').classList.remove('hidden');
            
            const autoShow = localStorage.getItem('greAutoShowSentences') === 'true';
            if (wordObj.example) {
                if (mode === 'mcq' || (mode === 'flashcard' && autoShow)) {
                    document.getElementById('card-front-example').classList.remove('hidden');
                } else {
                    document.getElementById('card-front-example').classList.add('hidden');
                }
            } else {
                document.getElementById('card-front-example').classList.add('hidden');
            }
            document.getElementById('card-back-example').classList.add('hidden');
            
            if (wordObj.example || mode === 'mcq' || mode === 'fillblanks') {
                document.getElementById('example-btn-front').classList.remove('hidden');
                document.getElementById('example-btn-back').classList.remove('hidden');
                
                const exampleSentence = (mode === 'flashcard' || mode === 'mcq') ? wordObj.example : (wordObj.long_example || wordObj.example);
                if (exampleSentence) {
                    // For the front and back, replace the word (plus any alphabetical suffixes) with its bold lowercase version
                    let regex = new RegExp("(" + escapeRegExp(wordObj.word) + "[a-zA-Z]*)", "gi");
                    let frontExample = exampleSentence.replace(regex, (match) => `<strong class="font-bold text-slate-800 dark:text-white">${match}</strong>`);
                    let backExample = exampleSentence.replace(regex, (match) => `<strong class="font-bold text-white">${match}</strong>`);
                    
                    let voiceIconFront = ` <button onclick="pronounceSentence(event)" class="inline-flex items-center justify-center p-1.5 ml-1 rounded-full hover:bg-slate-100 dark:hover:bg-slate-700 text-slate-400 dark:text-slate-500 hover:text-primary-600 dark:hover:text-primary-400 transition-colors focus:outline-none align-middle" title="Pronounce sentence"><svg class="w-4 h-4 sm:w-5 sm:h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M15.536 8.464a5 5 0 010 7.072m2.828-9.9a9 9 0 010 12.728M5.586 15H4a1 1 0 01-1-1v-4a1 1 0 011-1h1.586l4.707-4.707C10.923 3.663 12 4.109 12 5v14c0 .891-1.077 1.337-1.707.707L5.586 15z"></path></svg></button>`;
                    let voiceIconBack = ` <button onclick="pronounceSentence(event)" class="inline-flex items-center justify-center p-1.5 ml-1 rounded-full hover:bg-white/20 text-primary-200 hover:text-white transition-colors focus:outline-none align-middle" title="Pronounce sentence"><svg class="w-4 h-4 sm:w-5 sm:h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M15.536 8.464a5 5 0 010 7.072m2.828-9.9a9 9 0 010 12.728M5.586 15H4a1 1 0 01-1-1v-4a1 1 0 011-1h1.586l4.707-4.707C10.923 3.663 12 4.109 12 5v14c0 .891-1.077 1.337-1.707.707L5.586 15z"></path></svg></button>`;
     
                    const frontExEl = document.getElementById('card-front-example');
                    const backExEl = document.getElementById('card-back-example');
                    
                    frontExEl.innerHTML = frontExample + voiceIconFront;
                    backExEl.innerHTML = backExample + voiceIconBack;
                    
                    // Re-trigger animation when switching words
                    frontExEl.classList.remove('fade-in-slow');
                    backExEl.classList.remove('fade-in-slow');
                    void frontExEl.offsetWidth; // force reflow
                    frontExEl.classList.add('fade-in-slow');
                    backExEl.classList.add('fade-in-slow');
                } else {
                    document.getElementById('card-front-example').innerHTML = '';
                    document.getElementById('card-back-example').innerHTML = '';
                }
            } else {
                document.getElementById('example-btn-front').classList.add('hidden');
                document.getElementById('example-btn-back').classList.add('hidden');
            }
 
            const hint = document.getElementById('flashcard-hint');
            const studyScreen = document.getElementById('study-screen');
            if (mode === 'matching') {
                if (studyScreen) {
                    studyScreen.classList.remove('flashcard-mode', 'mcq-mode', 'fillblanks-mode');
                    studyScreen.classList.add('matching-mode');
                }
                document.getElementById('card-container-wrapper').classList.add('hidden');
                document.getElementById('mcq-options').classList.add('hidden');
                document.getElementById('matching-container').classList.remove('hidden');
                hint.classList.add('hidden');
                generateMatchingRound();
            } else if (mode === 'mcq') {
                if (studyScreen) {
                    studyScreen.classList.remove('flashcard-mode', 'matching-mode', 'fillblanks-mode');
                    studyScreen.classList.add('mcq-mode');
                }
                document.getElementById('card-container-wrapper').classList.remove('hidden');
                document.getElementById('matching-container').classList.add('hidden');
                document.getElementById('mcq-options').classList.remove('hidden');
                hint.classList.add('hidden');
                generateMCQ(wordObj);
            } else if (mode === 'fillblanks') {
                if (studyScreen) {
                    studyScreen.classList.remove('flashcard-mode', 'matching-mode');
                    studyScreen.classList.add('mcq-mode', 'fillblanks-mode');
                }
                document.getElementById('card-front-word').classList.add('hidden');
                document.getElementById('card-front-example').classList.add('hidden');
                document.getElementById('card-front-fillblanks').classList.remove('hidden');
                
                document.getElementById('pronounce-btn-front').classList.add('hidden');
                document.getElementById('example-btn-front').classList.add('hidden');
                document.getElementById('example-btn-back').classList.add('hidden');
                
                document.getElementById('card-container-wrapper').classList.remove('hidden');
                document.getElementById('matching-container').classList.add('hidden');
                document.getElementById('mcq-options').classList.remove('hidden');
                hint.classList.add('hidden');
                
                const sentence = wordObj.long_example || wordObj.example;
                const match = getInflectedWordInfo(wordObj.word, sentence);
                if (match) {
                    const suffix = match.text.substring(match.lcpLength);
                    let blankHTML = '';
                    if (suffix) {
                        const dispSuffix = (suffix === 'ed' || suffix === 'd') ? '(e)d' : suffix;
                        blankHTML = `<span class="font-mono font-bold text-slate-400 dark:text-neutral-500 tracking-widest select-none">_____</span>` +
                            `<span class="text-primary-600 dark:text-primary-400 font-sans font-semibold select-none">${dispSuffix}</span>`;
                    } else {
                        blankHTML = `<span class="font-mono font-bold text-slate-400 dark:text-neutral-500 tracking-widest select-none">_____</span>`;
                    }
                    let beforeText = sentence.substring(0, match.index);
                    beforeText = beforeText.replace(/\b(an|a)\s+$/i, (m, p1) => {
                        const isCapital = p1[0] === 'A';
                        return (isCapital ? 'A(n)' : 'a(n)') + ' ';
                    });
                    const afterText = sentence.substring(match.index + match.length);
                    document.getElementById('card-front-fillblanks').innerHTML = beforeText + blankHTML + afterText;
                } else {
                    const wordRegex = new RegExp(`\\b(an|a)\\s+(${escapeRegExp(wordObj.word)})\\b`, 'gi');
                    let sentenceUpdated = sentence.replace(wordRegex, (m, p1, p2) => {
                        const isCapital = p1[0] === 'A';
                        return (isCapital ? 'A(n)' : 'a(n)') + ' ' + `<span class="font-mono font-bold text-slate-400 dark:text-neutral-500 mx-1 select-none">_____</span>`;
                    });
                    if (sentenceUpdated === sentence) {
                        sentenceUpdated = sentence.replace(new RegExp(escapeRegExp(wordObj.word), "gi"), `<span class="font-mono font-bold text-slate-400 dark:text-neutral-500 mx-1 select-none">_____</span>`);
                    }
                    document.getElementById('card-front-fillblanks').innerHTML = sentenceUpdated;
                }
                generateFillBlanks(wordObj);
            } else {
                if (studyScreen) {
                    studyScreen.classList.add('flashcard-mode');
                    studyScreen.classList.remove('mcq-mode', 'matching-mode', 'fillblanks-mode');
                }
                document.getElementById('card-container-wrapper').classList.remove('hidden');
                document.getElementById('matching-container').classList.add('hidden');
                document.getElementById('mcq-options').classList.add('hidden');
                hint.classList.remove('hidden');
            }
         }
 
        function handleCardClick() {
            if (mode === 'matching' || mode === 'fillblanks') return;
            if (justTossed) return;
            if (preventNextFlip) {
                preventNextFlip = false;
                return;
            }
            if (window.getSelection().toString().length > 0) return;
            if (isSessionComplete) return;
            if (mode === 'mcq' && !isAnswered) return; 
            
            const cardEl = document.getElementById('flashcard');
            isFlipped = !isFlipped;
            
            const disclaimer = document.getElementById('swipe-disclaimer');
            if (isFlipped) {
                cardEl.classList.add('flipped');
                cardEl.style.touchAction = 'none'; // allow scroll if needed once flipped
                document.getElementById('flashcard-hint').classList.add('opacity-0');
                if (disclaimer && mode === 'flashcard') disclaimer.classList.remove('hidden');
                if (mode === 'flashcard') {
                    // Show example on the back automatically when flipped
                    const wordObj = appData[currentIndex];
                    if (wordObj.example) {
                        document.getElementById('card-back-example').classList.remove('hidden');
                    }
                    
                    document.getElementById('flashcard-rating-controls').classList.remove('hidden');
                    document.getElementById('flashcard-rating-controls').classList.add('flex');
                    
                    showNavControls();

                    // Auto-pronounce word if enabled (only once per card reveal, after flipping)
                    const autoPronounce = localStorage.getItem('greAutoPronounce') === 'true';
                    if (autoPronounce && !hasAutoPronouncedThisCard) {
                        hasAutoPronouncedThisCard = true;
                        pronounceWord();
                    }
                }
            } else {
                cardEl.classList.remove('flipped');
                cardEl.style.touchAction = 'none'; // non-scrollable before flipped
                document.getElementById('flashcard-hint').classList.remove('opacity-0');
                if (disclaimer) disclaimer.classList.add('hidden');
            }
        }

        function pronounceWord(e) {
            if (e) e.stopPropagation(); 
            if (!('speechSynthesis' in window)) return;

            // In Fill in the Blanks mode, the sound button reads the whole
            // sentence back (with the word filled in) rather than just the word.
            if (mode === 'fillblanks') {
                pronounceSentence(e);
                return;
            }
            
            // Cancel any ongoing speech
            window.speechSynthesis.cancel();
            
            const currentWord = appData[currentIndex].word;
            const utterance = new SpeechSynthesisUtterance(currentWord);
            utterance.lang = 'en-US';
            utterance.rate = 0.9; 
            window.speechSynthesis.speak(utterance);
        }

        function pronounceSentence(e) {
            if (e) e.stopPropagation(); 
            if (!('speechSynthesis' in window)) return;
            
            window.speechSynthesis.cancel();
            
            const currentWordObj = appData[currentIndex];
            const sentence = (mode === 'flashcard' || mode === 'mcq') ? currentWordObj.example : (currentWordObj.long_example || currentWordObj.example);
            if (!sentence) {
                // If there's no sentence, fall back to pronouncing the word
                const currentWord = currentWordObj.word;
                const utterance = new SpeechSynthesisUtterance(currentWord);
                utterance.lang = 'en-US';
                utterance.rate = 0.9;
                window.speechSynthesis.speak(utterance);
                return;
            }
            
            const utterance = new SpeechSynthesisUtterance(sentence);
            utterance.lang = 'en-US';
            utterance.rate = 1.4; 
            window.speechSynthesis.speak(utterance);
        }

        function toggleExample(e, side) {
            e.stopPropagation();
            if (mode === 'mcq') {
                toggleCardCollapse(e);
                return;
            }
            if (side === 'front') {
                document.getElementById('card-front-example').classList.toggle('hidden');
            } else {
                document.getElementById('card-back-example').classList.toggle('hidden');
            }
        }

        function toggleCardCollapse(e) {
            if (e) e.stopPropagation();
            isCardCollapsed = !isCardCollapsed;
            const container = document.getElementById('card-container');
            const btns = [document.getElementById('example-btn-front'), document.getElementById('example-btn-back')];
            if (isCardCollapsed) {
                container.classList.add('card-collapsed');
                btns.forEach(btn => {
                    if (btn) btn.title = "Expand Card";
                });
            } else {
                container.classList.remove('card-collapsed');
                btns.forEach(btn => {
                    if (btn) btn.title = "Collapse Card";
                });
            }
        }

        // =========================================================
        // DRAG MATCH MODE FUNCTIONS
        // =========================================================

        function pronounceCustomWord(e, word) {
            if (e) e.stopPropagation();
            if (!('speechSynthesis' in window)) return;
            window.speechSynthesis.cancel();
            const utterance = new SpeechSynthesisUtterance(word);
            utterance.lang = 'en-US';
            utterance.rate = 0.9;
            window.speechSynthesis.speak(utterance);
        }

        function pronounceCustomSentence(e, sentence) {
            if (e) e.stopPropagation();
            if (!('speechSynthesis' in window)) return;
            window.speechSynthesis.cancel();
            const utterance = new SpeechSynthesisUtterance(sentence);
            utterance.lang = 'en-US';
            utterance.rate = 1.4;
            window.speechSynthesis.speak(utterance);
        }

        function generateMatchingRound() {
            matchedCount = 0;
            matchingMistakes.clear();
            selectedWordEl = null;
            
            if (successLiftTimeout) {
                clearTimeout(successLiftTimeout);
                successLiftTimeout = null;
            }
            
            const inst = document.getElementById('matching-instruction');
            if (inst) {
                inst.innerText = 'Drag words to their correct definitions';
                inst.classList.remove('animate-pulse', 'text-primary-600', 'dark:text-primary-400', 'font-semibold');
                inst.classList.add('text-slate-400', 'dark:text-slate-500', 'font-medium');
            }
            
            const defsCol = document.getElementById('matching-defs-column');
            if (defsCol) {
                defsCol.style.transition = 'none';
                defsCol.classList.remove('success-lift');
                void defsCol.offsetHeight;
                defsCol.style.transition = '';
            }
            
            const gridWrapper = document.getElementById('matching-grid-wrapper');
            if (gridWrapper) {
                gridWrapper.style.transition = 'none';
                gridWrapper.classList.remove('success-grid');
                void gridWrapper.offsetHeight;
                gridWrapper.style.transition = '';
            }
            
            const targetWord = appData[currentIndex];
            const targetType = targetWord.type;
            
            // Build an index-annotated pool of same-type words so each entry is uniquely identifiable
            const sameTypePool = appData.map((w, i) => ({ ...w, _idx: i })).filter(w => w.type === targetType);
            
            // Filter out words that have already been matched, except the current targetWord (by index)
            const unmatchedPool = sameTypePool.filter(w => w._idx === currentIndex || !sessionMatchedIndices.has(w._idx));
            
            // Annotate the target with its index
            const targetWithIdx = { ...targetWord, _idx: currentIndex };
            
            let selection = [];
            if (unmatchedPool.length >= 4) {
                // Ensure targetWord is first in the list
                selection = [targetWithIdx];
                const remainingPool = unmatchedPool.filter(w => w._idx !== currentIndex);
                
                // Prefer non-mastered words as distractors
                const nonMasteredRemaining = remainingPool.filter(w => !isMasteredWord(w));
                const preferredPool = nonMasteredRemaining.length >= 3 ? nonMasteredRemaining : remainingPool;
                
                // Shuffle remaining and pick 3
                const shuffledRemaining = preferredPool.sort(() => 0.5 - Math.random());
                selection = selection.concat(shuffledRemaining.slice(0, 3));
            } else {
                // Just use whatever unmatched same-type words are left in this set (can be 1, 2, or 3)
                selection = unmatchedPool;
            }
            
            currentMatchingWords = selection;
            
            // Update progress header for matching mode
            updateSessionProgress();

            
            // Update badge/type display
            document.getElementById('matching-type-badge').innerText = targetType || 'Word';
            
            renderMatchingUI();
        }

        function renderMatchingUI() {
            const wordsCol = document.getElementById('matching-words-column');
            const defsCol = document.getElementById('matching-defs-column');
            
            wordsCol.innerHTML = '';
            defsCol.innerHTML = '';
            
            // Shuffle word chips and definitions independently
            const shuffledWords = [...currentMatchingWords].sort(() => 0.5 - Math.random());
            const shuffledDefs = [...currentMatchingWords].sort(() => 0.5 - Math.random());
            
            shuffledWords.forEach(wordObj => {
                const chip = document.createElement('div');
                chip.className = 'matching-word-chip cursor-pointer select-none bg-white dark:bg-neutral-900 border-2 border-slate-200 dark:border-neutral-800 px-5 py-3.5 rounded-xl flex items-center justify-center font-bold text-black dark:text-slate-200 shadow-sm transition-all hover:border-primary-400 touch-none flex-grow md:flex-grow-0 min-w-[120px] text-sm sm:text-base whitespace-nowrap relative';
                chip.setAttribute('data-word', wordObj.word);
                chip.setAttribute('data-idx', String(wordObj._idx));
                
                // Add the word text
                const textSpan = document.createElement('span');
                textSpan.innerText = formatWordBySetting(wordObj.word);
                chip.appendChild(textSpan);

                // Add a small speaker button absolute-positioned in the top-left
                const speakBtn = document.createElement('button');
                speakBtn.className = 'absolute top-1 left-1 p-1 rounded-full text-slate-400 hover:text-primary-600 hover:bg-slate-100 dark:text-slate-500 dark:hover:text-primary-400 dark:hover:bg-neutral-800 transition-colors focus:outline-none flex items-center justify-center';
                speakBtn.title = 'Pronounce word';
                speakBtn.addEventListener('pointerdown', (e) => {
                    e.stopPropagation();
                });
                speakBtn.addEventListener('click', (e) => {
                    e.stopPropagation();
                    pronounceCustomWord(e, wordObj.word);
                });
                speakBtn.innerHTML = `
                    <svg class="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M15.536 8.464a5 5 0 010 7.072m2.828-9.9a9 9 0 010 12.728M5.586 15H4a1 1 0 01-1-1v-4a1 1 0 011-1h1.586l4.707-4.707C10.923 3.663 12 4.109 12 5v14c0 .891-1.077 1.337-1.707.707L5.586 15z"></path>
                    </svg>
                `;
                chip.appendChild(speakBtn);
                
                setupDraggable(chip, wordObj);
                
                wordsCol.appendChild(chip);
            });
            
            shuffledDefs.forEach(wordObj => {
                const card = document.createElement('div');
                card.className = 'matching-card w-full cursor-pointer select-none';
                
                let regex = new RegExp("(" + escapeRegExp(wordObj.word) + "[a-zA-Z]*)", "gi");
                let boldExample = wordObj.example ? wordObj.example.replace(regex, (match) => `<strong class="font-bold text-emerald-950 dark:text-white">${match}</strong>`) : "No example sentence available.";
                
                card.innerHTML = `
                    <div class="matching-card-inner">
                        <!-- Front Face: Definition -->
                        <div class="matching-drop-zone card-face bg-white dark:bg-neutral-900 border-2 border-dashed border-slate-200 dark:border-neutral-800 py-3.5 px-5 rounded-xl text-slate-600 dark:text-slate-300 min-h-[80px] sm:min-h-[92px] flex items-center justify-center text-center text-sm sm:text-[15.5px] font-medium shadow-sm transition-all duration-200" data-correct-idx="${wordObj._idx}">
                            ${wordObj.def}
                        </div>
                        <!-- Back Face: Example Sentence -->
                        <div class="card-face rotate-y-180 bg-emerald-50 dark:bg-emerald-950/20 border-2 border-solid border-emerald-500 py-3.5 pr-8 pl-5 rounded-xl text-emerald-800 dark:text-emerald-300 min-h-[80px] sm:min-h-[92px] flex items-center justify-center text-center text-sm sm:text-base font-medium shadow-sm relative">
                            <span>${boldExample}</span>
                        </div>
                    </div>
                `;

                // Add Pronounce Example Button
                const backFace = card.querySelector('.card-face.rotate-y-180');
                const backSpeakBtn = document.createElement('button');
                backSpeakBtn.className = 'absolute top-2 right-2 p-1.5 rounded-full hover:bg-white/20 text-emerald-700 dark:text-emerald-300 hover:text-emerald-950 dark:hover:text-white transition-colors focus:outline-none z-10 flex items-center justify-center';
                backSpeakBtn.title = 'Pronounce example sentence';
                backSpeakBtn.innerHTML = `
                    <svg class="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M15.536 8.464a5 5 0 010 7.072m2.828-9.9a9 9 0 010 12.728M5.586 15H4a1 1 0 01-1-1v-4a1 1 0 011-1h1.586l4.707-4.707C10.923 3.663 12 4.109 12 5v14c0 .891-1.077 1.337-1.707.707L5.586 15z"></path>
                    </svg>
                `;
                backSpeakBtn.addEventListener('pointerdown', (e) => {
                    e.stopPropagation();
                });
                backSpeakBtn.addEventListener('click', (e) => {
                    e.stopPropagation();
                    if (wordObj.example) {
                        pronounceCustomSentence(e, wordObj.example);
                    }
                });
                backFace.appendChild(backSpeakBtn);
                
                card.addEventListener('click', (e) => {
                    if (card.classList.contains('matched')) {
                        const cardInner = card.querySelector('.matching-card-inner');
                        if (cardInner) {
                            cardInner.classList.toggle('flipped');
                        }
                    }
                });
                
                const dropZone = card.querySelector('.matching-drop-zone');
                setupDropZone(dropZone, wordObj);
                
                defsCol.appendChild(card);
            });
        }

        function setupDraggable(chip, wordObj) {
            chip.addEventListener('pointerdown', (e) => {
                if (matchedCount === currentMatchingWords.length) return;
                if (activeDragPointerId !== null) return;
                
                if (selectedWordEl) {
                    selectedWordEl.classList.remove('border-primary-500', 'dark:border-primary-500', 'bg-primary-50/50', 'dark:bg-primary-950/20');
                }
                selectedWordEl = chip;
                chip.classList.add('border-primary-500', 'dark:border-primary-500', 'bg-primary-50/50', 'dark:bg-primary-950/20');
                
                activeDragPointerId = e.pointerId;
                activeDragEl = chip;
                activeDragWordObj = wordObj;
                
                initialX = e.clientX;
                initialY = e.clientY;
                
                chip.setPointerCapture(e.pointerId);
                chip.style.transition = 'none';
                chip.style.zIndex = '50';
            });
            
            chip.addEventListener('pointermove', (e) => {
                if (activeDragEl !== chip || activeDragPointerId !== e.pointerId) return;
                
                const deltaX = e.clientX - initialX;
                const deltaY = e.clientY - initialY;
                
                chip.style.transform = `translate3d(${deltaX}px, ${deltaY}px, 0)`;
                
                const zones = document.querySelectorAll('.matching-drop-zone');
                zones.forEach(zone => {
                    const card = zone.closest('.matching-card');
                    if (card && card.classList.contains('matched')) return;
                    
                    const rect = zone.getBoundingClientRect();
                    if (e.clientX >= rect.left && e.clientX <= rect.right && e.clientY >= rect.top && e.clientY <= rect.bottom) {
                        zone.classList.add('bg-primary-50/30', 'dark:bg-primary-900/20', 'border-primary-500');
                    } else {
                        zone.classList.remove('bg-primary-50/30', 'dark:bg-primary-900/20', 'border-primary-500');
                    }
                });
            });
            
            chip.addEventListener('pointerup', (e) => {
                if (activeDragEl !== chip || activeDragPointerId !== e.pointerId) return;
                
                activeDragPointerId = null;
                activeDragEl = null;
                activeDragWordObj = null;
                
                try {
                    chip.releasePointerCapture(e.pointerId);
                } catch (err) {}
                
                chip.style.transition = 'transform 0.2s ease';
                chip.style.zIndex = '';
                
                let droppedZone = null;
                const zones = document.querySelectorAll('.matching-drop-zone');
                zones.forEach(zone => {
                    const card = zone.closest('.matching-card');
                    if (card && card.classList.contains('matched')) return;
                    
                    const rect = zone.getBoundingClientRect();
                    if (e.clientX >= rect.left && e.clientX <= rect.right && e.clientY >= rect.top && e.clientY <= rect.bottom) {
                        droppedZone = zone;
                    }
                    zone.classList.remove('bg-primary-50/30', 'dark:bg-primary-900/20', 'border-primary-500');
                });
                
                if (droppedZone) {
                    const correctIdx = parseInt(droppedZone.getAttribute('data-correct-idx'), 10);
                    if (correctIdx === wordObj._idx) {
                        if (selectedWordEl === chip) selectedWordEl = null;
                        handleMatchSuccess(chip, droppedZone, wordObj, false);
                    } else {
                        chip.style.transform = 'translate3d(0, 0, 0)';
                        const correctWordObj = currentMatchingWords.find(w => w._idx === correctIdx);
                        handleMatchFailure(chip, droppedZone, wordObj, correctWordObj);
                    }
                } else {
                    chip.style.transform = 'translate3d(0, 0, 0)';
                }
            });
            
            chip.addEventListener('pointercancel', (e) => {
                if (activeDragEl !== chip || activeDragPointerId !== e.pointerId) return;
                activeDragPointerId = null;
                activeDragEl = null;
                activeDragWordObj = null;
                
                try {
                    chip.releasePointerCapture(e.pointerId);
                } catch (err) {}
                
                chip.style.transition = 'transform 0.2s ease';
                chip.style.transform = 'translate3d(0, 0, 0)';
                chip.style.zIndex = '';
                
                const zones = document.querySelectorAll('.matching-drop-zone');
                zones.forEach(zone => {
                    zone.classList.remove('bg-primary-50/30', 'dark:bg-primary-900/20', 'border-primary-500');
                });
            });
        }

        function setupDropZone(zone, correctWordObj) {
            zone.addEventListener('click', (e) => {
                e.stopPropagation();
                const card = zone.closest('.matching-card');
                if (card && card.classList.contains('matched')) return;
                if (matchedCount === currentMatchingWords.length) return;
                if (zone.classList.contains('pointer-events-none')) return;
                
                if (selectedWordEl) {
                    const selectedIdx = parseInt(selectedWordEl.getAttribute('data-idx'), 10);
                    const correctIdx = correctWordObj._idx;
                    const selectedWordObj = currentMatchingWords.find(w => w._idx === selectedIdx);
                    
                    if (selectedIdx === correctIdx) {
                        const chip = selectedWordEl;
                        selectedWordEl.classList.remove('border-primary-500', 'dark:border-primary-500', 'bg-primary-50/50', 'dark:bg-primary-950/20');
                        selectedWordEl = null;
                        handleMatchSuccess(chip, zone, selectedWordObj, true);
                    } else {
                        const chip = selectedWordEl;
                        selectedWordEl.classList.remove('border-primary-500', 'dark:border-primary-500', 'bg-primary-50/50', 'dark:bg-primary-950/20');
                        selectedWordEl = null;
                        handleMatchFailure(chip, zone, selectedWordObj, correctWordObj);
                    }
                }
            });
        }

        function handleMatchSuccess(wordChip, dropZone, wordObj, isClickMatch = false) {
            // Fade out and scale down the matched wordChip
            if (isClickMatch) {
                // Calculate distance between chip and zone
                const chipRect = wordChip.getBoundingClientRect();
                const zoneRect = dropZone.getBoundingClientRect();
                const deltaX = (zoneRect.left + zoneRect.width / 2) - (chipRect.left + chipRect.width / 2);
                const deltaY = (zoneRect.top + zoneRect.height / 2) - (chipRect.top + chipRect.height / 2);
                
                wordChip.style.zIndex = '50';
                wordChip.style.transition = 'transform 0.45s cubic-bezier(0.25, 1, 0.5, 1), opacity 0.4s ease';
                wordChip.style.transform = `translate3d(${deltaX}px, ${deltaY}px, 0) scale(0.65)`;
                wordChip.style.opacity = '0';
                wordChip.style.pointerEvents = 'none';
            } else {
                wordChip.style.transition = 'transform 0.4s ease, opacity 0.4s ease';
                wordChip.style.transform = `${wordChip.style.transform} scale(0)`;
                wordChip.style.opacity = '0';
                wordChip.style.pointerEvents = 'none';
            }
            
            const card = dropZone.closest('.matching-card');
            if (card) {
                card.classList.add('matched');
            }
            
            // Flip the closest card to show only the example sentence on the back
            dropZone.style.pointerEvents = 'none';
            const cardInner = card ? card.querySelector('.matching-card-inner') : null;
            if (cardInner) {
                cardInner.classList.add('flipped');
            }
            
            const idx = wordObj._idx;
            if (idx !== undefined && idx !== -1) {
                sessionMatchedIndices.add(idx);
                updateSessionProgress();
                completeWord(idx);
            }
            
            matchedCount++;
            
            const madeMistake = matchingMistakes.has(wordObj.word);
            addToLastSeen(wordObj, !madeMistake);
            
            if (madeMistake) {
                recordWordGameStatus(wordObj.word, 'bookmarked');
            } else {
                recordWordGameStatus(wordObj.word, 'mastered');
            }
            
            // Update words in review: remove from missedWordsDB if matched correctly in review mode
            if (isReviewMode && !madeMistake) {
                delete missedWordsDB[wordObj.word];
                localStorage.setItem('greMissedWords', JSON.stringify(missedWordsDB));
                hasUnsavedChanges = true;
            } else if (!isReviewMode && catSelect.value === 'Random' && !madeMistake) {
                progressDB['RM_' + wordObj.word] = true;
                localStorage.setItem('greProgressDB', JSON.stringify(progressDB));
                hasUnsavedChanges = true;
            }
            
            if (matchedCount === currentMatchingWords.length) {
                document.getElementById('next-btn').disabled = false;
                showNavControls();
                
                const inst = document.getElementById('matching-instruction');
                if (inst) {
                    inst.innerText = 'Click a card to view definition';
                    inst.classList.remove('text-slate-400', 'dark:text-slate-500', 'font-medium');
                    inst.classList.add('animate-pulse', 'text-primary-600', 'dark:text-primary-400', 'font-semibold');
                }
                
                successLiftTimeout = setTimeout(() => {
                    const defsCol = document.getElementById('matching-defs-column');
                    const gridWrapper = document.getElementById('matching-grid-wrapper');
                    const isDesktop = window.matchMedia('(min-width: 768px)').matches;
                    if (isDesktop && gridWrapper) {
                        // Desktop: animate parent into centered 2x2 grid
                        gridWrapper.classList.add('success-grid');
                    } else if (defsCol) {
                        // Mobile: simple lift up
                        defsCol.classList.add('success-lift');
                    }
                    successLiftTimeout = null;
                }, 400);
            }
        }

        // Incorrect drop zone handler
        function handleMatchFailure(wordChip, dropZone, wordObj, correctWordObj) {
            matchingMistakes.add(wordObj.word);
            matchingMistakes.add(correctWordObj.word);
            
            // Only add the dragged word to missed words (not the drop zone's word which wasn't attempted)
            if (!(wordObj.word in missedWordsDB)) {
                missedWordsDB[wordObj.word] = getWordIndex(wordObj);
                localStorage.setItem('greMissedWords', JSON.stringify(missedWordsDB));
                hasUnsavedChanges = true;
            }
            recordWordGameStatus(wordObj.word, 'bookmarked');
            
            const card = dropZone.closest('.matching-card');
            
            wordChip.classList.add('animate-shake', 'border-red-500', 'dark:border-red-500');
            if (card) card.classList.add('animate-shake');
            dropZone.classList.add('border-red-500', 'dark:border-red-500');
            
            setTimeout(() => {
                wordChip.classList.remove('animate-shake', 'border-red-500', 'dark:border-red-500');
                if (card) card.classList.remove('animate-shake');
                dropZone.classList.remove('border-red-500', 'dark:border-red-500');
            }, 500);
        }

        // Helper: check if a word is "mastered" (seen in a completed/progressed set and NOT in missedWordsDB)
        function isMasteredWord(wordObj) {
            if (wordObj.word in missedWordsDB) return false;
            // Check if the word appears in any set that has been progressed past it
            for (const cat of Object.keys(vocabularyDB)) {
                for (const set of Object.keys(vocabularyDB[cat])) {
                    const setWords = vocabularyDB[cat][set];
                    const progressKey = `${cat}|${set}`;
                    const progressVal = progressDB[progressKey];
                    let seenCount = 0;
                    if (progressVal === 'COMPLETED') seenCount = setWords.length;
                    else if (progressVal > 0) seenCount = parseInt(progressVal);
                    const idx = setWords.indexOf(wordObj);
                    if (idx !== -1 && idx < seenCount) return true;
                }
            }
            // Also check Random mode mastery
            if (progressDB['RM_' + wordObj.word]) return true;
            return false;
        }


        function generateMCQ(correctWord) {
            const mcqOptions = document.getElementById('mcq-options');
            mcqOptions.innerHTML = '';
            
            let allWordsFlat = [];
            Object.values(vocabularyDB).forEach(cat => {
                Object.values(cat).forEach(set => { allWordsFlat = allWordsFlat.concat(set); });
            });
            if(allWordsFlat.length < 4) allWordsFlat = appData;

            // Filter wrong options to be of the same type (noun, verb, adj., etc.)
            let pool = allWordsFlat.filter(w => w.word !== correctWord.word && w.type === correctWord.type);
            // Fallback if there aren't enough words of the same type
            if (pool.length < 3) {
                pool = allWordsFlat.filter(w => w.word !== correctWord.word);
            }

            // Prefer non-mastered words as distractors
            const nonMastered = pool.filter(w => !isMasteredWord(w));
            if (nonMastered.length >= 3) {
                pool = nonMastered;
            }
            
            pool = pool.sort(() => 0.5 - Math.random());
            let options = [correctWord.def, ...pool.slice(0, 3).map(w => w.def)].sort(() => 0.5 - Math.random());

            options.forEach(opt => {
                const btn = document.createElement('button');
                btn.className = 'option-btn select-none relative overflow-hidden bg-white dark:bg-neutral-900 border-2 border-slate-200 dark:border-neutral-800 p-[14px] sm:p-[18px] rounded-xl text-left text-[15.5px] sm:text-[17.5px] text-slate-700 dark:text-slate-200 hover:border-primary-400 dark:hover:border-primary-500 hover:bg-primary-50 dark:hover:bg-slate-700 focus:outline-none transition-all font-medium leading-relaxed shadow-sm';
                btn.innerText = opt;
                btn.onclick = (e) => { e.stopPropagation(); handleMCQGuess(btn, opt === correctWord.def); };
                mcqOptions.appendChild(btn);
            });
        }

        function handleMCQGuess(selectedBtn, isCorrect) {
            if (isAnswered) return;
            isAnswered = true;
            const currentWordObj = appData[currentIndex];
            addToLastSeen(currentWordObj, isCorrect);

            if (!isCorrect) {
                missedWordsDB[currentWordObj.word] = getWordIndex(currentWordObj);
                localStorage.setItem('greMissedWords', JSON.stringify(missedWordsDB));
                hasUnsavedChanges = true;
                recordWordGameStatus(currentWordObj.word, 'bookmarked');
                if (isReviewMode) {
                    const tossed = appData.splice(currentIndex, 1)[0];
                    appData.push(tossed);
                    reviewTossPending = true;
                }
            } else if (isReviewMode && isCorrect) {
                delete missedWordsDB[currentWordObj.word];
                localStorage.setItem('greMissedWords', JSON.stringify(missedWordsDB));
                hasUnsavedChanges = true;
                reviewCorrectCount++;
                recordWordGameStatus(currentWordObj.word, 'mastered');
            }

            // Save progress immediately in Quiz mode on every answer
            if (!isReviewMode) {
                completeWord(currentIndex);
                if (isCorrect) {
                    recordWordGameStatus(currentWordObj.word, 'mastered');
                    if (catSelect.value === 'Random') {
                        progressDB['RM_' + currentWordObj.word] = true;
                        localStorage.setItem('greProgressDB', JSON.stringify(progressDB));
                        hasUnsavedChanges = true;
                    }
                }
            }

            document.querySelectorAll('.option-btn').forEach(btn => {
                btn.disabled = true;
                btn.classList.remove('border-slate-200', 'dark:border-neutral-800', 'hover:border-primary-400', 'dark:hover:border-primary-500', 'hover:bg-primary-50', 'dark:hover:bg-slate-700', 'cursor-pointer', 'transition-all');
                btn.classList.add('cursor-default');
                
                if (btn.innerText === currentWordObj.def) {
                    btn.classList.add('border-emerald-500', 'dark:border-emerald-500', 'bg-emerald-50', 'dark:bg-emerald-900/30', 'text-emerald-900', 'dark:text-emerald-300');
                } else if (btn === selectedBtn && !isCorrect) {
                    btn.classList.add('border-red-500', 'dark:border-red-500');
                } else {
                    btn.classList.add('border-primary-400', 'dark:border-primary-500', 'opacity-40', 'dark:opacity-30', 'bg-slate-50', 'dark:bg-black');
                }
            });

            // Expand the card if it was collapsed
            if (isCardCollapsed) {
                isCardCollapsed = false;
                const container = document.getElementById('card-container');
                if (container) container.classList.remove('card-collapsed');
                const btns = [document.getElementById('example-btn-front'), document.getElementById('example-btn-back')];
                btns.forEach(btn => {
                    if (btn) btn.title = "Collapse Card";
                });
            }

            isFlipped = true;
            document.getElementById('flashcard').classList.add('flipped');
            
            // Show example sentence automatically on the back after picking an option
            if (currentWordObj.example) {
                document.getElementById('card-back-example').classList.remove('hidden');
            }
            
            // FIX: Fade in the wrapper while unhiding the next button
            document.getElementById('next-btn').disabled = false;
            showNavControls();

            // Auto-pronounce word if enabled (only once per card reveal, after guessing)
            const autoPronounce = localStorage.getItem('greAutoPronounce') === 'true';
            if (autoPronounce && !hasAutoPronouncedThisCard) {
                hasAutoPronouncedThisCard = true;
                pronounceWord();
            }
        }

        function processSelfRating(knewIt) {
            const currentWordObj = appData[currentIndex];
            addToLastSeen(currentWordObj, knewIt);
            if (!knewIt) {
                missedWordsDB[currentWordObj.word] = getWordIndex(currentWordObj);
                localStorage.setItem('greMissedWords', JSON.stringify(missedWordsDB));
                hasUnsavedChanges = true;
                recordWordGameStatus(currentWordObj.word, 'bookmarked');
                if (isReviewMode) {
                    appData.splice(currentIndex, 1);
                    appData.push(currentWordObj);
                    renderCard();
                    return;
                }
            } else if (isReviewMode && knewIt) {
                delete missedWordsDB[currentWordObj.word];
                localStorage.setItem('greMissedWords', JSON.stringify(missedWordsDB));
                hasUnsavedChanges = true;
                reviewCorrectCount++;
                recordWordGameStatus(currentWordObj.word, 'mastered');
            } else if (!isReviewMode && catSelect.value === 'Random' && knewIt) {
                progressDB['RM_' + currentWordObj.word] = true;
                localStorage.setItem('greProgressDB', JSON.stringify(progressDB));
                hasUnsavedChanges = true;
                recordWordGameStatus(currentWordObj.word, 'mastered');
            } else {
                recordWordGameStatus(currentWordObj.word, 'mastered');
            }
            nextWord();
        }

        // =========================================================
        // FILL THE BLANKS GAME MODE LOGIC
        // =========================================================
        function getInflectedWordInfo(word, sentence) {
            const cleanWord = word.trim().toLowerCase();
            const lowerSentence = sentence.toLowerCase();
            
            // Check for exact substring match first if it's a whole-word match (fast & accurate for non-inflected)
            const exactIdx = lowerSentence.indexOf(cleanWord);
            if (exactIdx !== -1) {
                const charBefore = exactIdx > 0 ? sentence[exactIdx - 1] : '';
                const charAfter = exactIdx + word.length < sentence.length ? sentence[exactIdx + word.length] : '';
                const isWordBoundary = !/[a-zA-Z]/.test(charBefore) && !/[a-zA-Z]/.test(charAfter);
                
                if (isWordBoundary) {
                    return {
                        index: exactIdx,
                        length: word.length,
                        text: sentence.substring(exactIdx, exactIdx + word.length),
                        lcpLength: word.length
                    };
                }
            }
            
            // If not found exactly (e.g. inflected: "abased" for "abase"),
            // token-based prefix matching
            const regex = /\b[a-zA-Z-]+\b/g;
            let match;
            let bestMatch = null;
            let bestScore = 0;
            
            while ((match = regex.exec(sentence)) !== null) {
                const token = match[0];
                const cleanToken = token.toLowerCase();
                
                // Compute LCP
                let lcp = "";
                const minLen = Math.min(cleanWord.length, cleanToken.length);
                for (let i = 0; i < minLen; i++) {
                    if (cleanWord[i] === cleanToken[i]) {
                        lcp += cleanWord[i];
                    } else {
                        break;
                    }
                }
                
                // If LCP is significant, score it
                if (lcp.length >= Math.min(3, cleanWord.length)) {
                    let score = lcp.length;
                    if (score > bestScore) {
                        bestScore = score;
                        bestMatch = {
                            index: match.index,
                            length: token.length,
                            text: token,
                            lcpLength: lcp.length
                        };
                    }
                }
            }
            
            if (bestMatch) {
                return bestMatch;
            }
            
            return null;
        }

        function formatWordBySetting(word) {
            const wordCase = localStorage.getItem('greWordCase') || 'lowercase';
            if (wordCase === 'uppercase') {
                return word.toUpperCase();
            } else if (wordCase === 'capitalize') {
                return word.charAt(0).toUpperCase() + word.slice(1).toLowerCase();
            } else if (wordCase === 'lowercase') {
                return word.toLowerCase();
            }
            return word; // normal-case
        }

        function applySuffixToWord(word, suffix) {
            if (!suffix) return word;
            
            const cleanWord = word.trim().toLowerCase();
            const cleanSuffix = suffix.trim().toLowerCase();
            
            if (cleanSuffix === 'd' || cleanSuffix === 'ed') {
                if (cleanWord.endsWith('e')) {
                    return word + 'd';
                } else if (cleanWord.endsWith('y') && !cleanWord.endsWith('ey')) {
                    return word.slice(0, -1) + 'ied';
                } else {
                    return word + 'ed';
                }
            }
            
            if (cleanSuffix === 'ing') {
                if (cleanWord.endsWith('e') && !cleanWord.endsWith('ee')) {
                    return word.slice(0, -1) + 'ing';
                } else {
                    return word + 'ing';
                }
            }
            
            if (cleanSuffix === 's' || cleanSuffix === 'es' || cleanSuffix === 'ies') {
                if (cleanWord.endsWith('y') && !cleanWord.endsWith('ey')) {
                    return word.slice(0, -1) + 'ies';
                } else if (cleanWord.endsWith('sh') || cleanWord.endsWith('ch') || cleanWord.endsWith('x') || cleanWord.endsWith('s')) {
                    return word + 'es';
                } else {
                    return word + 's';
                }
            }
            
            return word + suffix;
        }

        function generateFillBlanks(correctWord) {
            const mcqOptions = document.getElementById('mcq-options');
            mcqOptions.innerHTML = '';
            
            let allWordsFlat = [];
            Object.values(vocabularyDB).forEach(cat => {
                Object.values(cat).forEach(set => { allWordsFlat = allWordsFlat.concat(set); });
            });
            
            // De-duplicate flat word list by word name
            const seen = new Set();
            const uniqueWordsFlat = [];
            allWordsFlat.forEach(w => {
                if (!seen.has(w.word)) {
                    seen.add(w.word);
                    uniqueWordsFlat.push(w);
                }
            });
            allWordsFlat = uniqueWordsFlat;
            
            if(allWordsFlat.length < 4) allWordsFlat = appData;

            // Filter wrong options to be of the same type (noun, verb, adj., etc.)
            let pool = allWordsFlat.filter(w => w.word !== correctWord.word && w.type === correctWord.type);
            // Fallback if there aren't enough words of the same type
            if (pool.length < 3) {
                pool = allWordsFlat.filter(w => w.word !== correctWord.word);
            }

            // Prefer non-mastered words as distractors
            const nonMastered = pool.filter(w => !isMasteredWord(w));
            if (nonMastered.length >= 3) {
                pool = nonMastered;
            }
            
            pool = pool.sort(() => 0.5 - Math.random());
            let options = [correctWord, ...pool.slice(0, 3)].sort(() => 0.5 - Math.random());

            // Extract the suffix to inflect options
            const sentence = correctWord.long_example || correctWord.example;
            const match = getInflectedWordInfo(correctWord.word, sentence);
            const suffix = match ? match.text.substring(match.lcpLength) : '';

            options.forEach(opt => {
                const btn = document.createElement('button');
                btn.className = 'option-btn select-none relative overflow-hidden bg-white dark:bg-neutral-900 border-2 border-slate-200 dark:border-neutral-800 p-[14px] sm:p-[18px] rounded-xl text-left text-slate-700 dark:text-slate-200 hover:border-primary-400 dark:hover:border-primary-500 hover:bg-primary-50 dark:hover:bg-slate-700 focus:outline-none transition-all font-medium leading-relaxed shadow-sm w-full';
                btn.dataset.originalWord = opt.word;
                btn.dataset.originalDef = opt.def;
                
                const wordSpan = document.createElement('span');
                wordSpan.className = 'word-label text-base sm:text-lg font-bold text-slate-800 dark:text-white';
                // Inflect all options with the suffix, then format case!
                const inflectedWord = applySuffixToWord(opt.word, suffix);
                wordSpan.innerText = formatWordBySetting(inflectedWord);
                btn.appendChild(wordSpan);
                
                const defSpan = document.createElement('span');
                defSpan.className = 'def-label text-xs sm:text-sm font-normal text-slate-500 dark:text-slate-400 hidden';
                defSpan.innerText = ' — ' + opt.def;
                btn.appendChild(defSpan);
                
                btn.onclick = (e) => { 
                    e.stopPropagation(); 
                    handleFillBlanksGuess(btn, opt, correctWord); 
                };
                mcqOptions.appendChild(btn);
            });
        }

        function handleFillBlanksGuess(selectedBtn, selectedWordObj, correctWordObj) {
            if (isAnswered) return;
            isAnswered = true;
            
            const isCorrect = (selectedWordObj.word === correctWordObj.word);
            addToLastSeen(correctWordObj, isCorrect);

            if (!isCorrect) {
                missedWordsDB[correctWordObj.word] = getWordIndex(correctWordObj);
                localStorage.setItem('greMissedWords', JSON.stringify(missedWordsDB));
                hasUnsavedChanges = true;
                recordWordGameStatus(correctWordObj.word, 'bookmarked');
                if (isReviewMode) {
                    const tossed = appData.splice(currentIndex, 1)[0];
                    appData.push(tossed);
                    reviewTossPending = true;
                }
            } else if (isReviewMode && isCorrect) {
                delete missedWordsDB[correctWordObj.word];
                localStorage.setItem('greMissedWords', JSON.stringify(missedWordsDB));
                hasUnsavedChanges = true;
                reviewCorrectCount++;
                recordWordGameStatus(correctWordObj.word, 'mastered');
            }

            // Save progress immediately on every answer so progress bar advances
            if (!isReviewMode) {
                completeWord(currentIndex);
                if (isCorrect) {
                    recordWordGameStatus(correctWordObj.word, 'mastered');
                    if (catSelect.value === 'Random') {
                        progressDB['RM_' + correctWordObj.word] = true;
                        localStorage.setItem('greProgressDB', JSON.stringify(progressDB));
                        hasUnsavedChanges = true;
                    }
                }
            }

            // Reveal definitions and color option buttons
            document.querySelectorAll('.option-btn').forEach(btn => {
                btn.disabled = true;
                btn.classList.remove('border-slate-200', 'dark:border-neutral-800', 'hover:border-primary-400', 'dark:hover:border-primary-500', 'hover:bg-primary-50', 'dark:hover:bg-slate-700', 'cursor-pointer', 'transition-all');
                btn.classList.add('cursor-default');
                
                const defLabel = btn.querySelector('.def-label');
                if (defLabel) defLabel.classList.remove('hidden');
                
                const originalWord = btn.dataset.originalWord.trim().toLowerCase();
                const correctWord = correctWordObj.word.trim().toLowerCase();
                const guessedWord = selectedWordObj.word.trim().toLowerCase();
                
                // Revert choices to base word according to settings
                const wordLabel = btn.querySelector('.word-label');
                if (wordLabel) {
                    wordLabel.innerText = formatWordBySetting(btn.dataset.originalWord);
                }
                
                if (originalWord === correctWord) {
                    btn.classList.add('border-emerald-500', 'dark:border-emerald-500', 'bg-emerald-50', 'dark:bg-emerald-900/30', 'text-emerald-900', 'dark:text-emerald-300');
                    if (wordLabel) wordLabel.classList.add('text-emerald-700', 'dark:text-emerald-300');
                } else if (originalWord === guessedWord && !isCorrect) {
                    btn.classList.add('border-red-500', 'dark:border-red-500', 'bg-red-50', 'dark:bg-red-900/30');
                    if (wordLabel) wordLabel.classList.add('text-red-700', 'dark:text-red-300');
                } else {
                    btn.classList.add('border-primary-400', 'dark:border-primary-500', 'opacity-60', 'dark:opacity-40', 'bg-slate-50', 'dark:bg-black');
                }
            });

            // Update the blank with the correct word, coloring only the root!
            const sentence = correctWordObj.long_example || correctWordObj.example;
            const match = getInflectedWordInfo(correctWordObj.word, sentence);
            
            if (match) {
                const root = match.text.substring(0, match.lcpLength);
                const suffix = match.text.substring(match.lcpLength);
                
                const colorClass = 'text-primary-600 dark:text-primary-400';
                const displayRoot = formatWordBySetting(root);
                const displaySuffix = formatWordBySetting(suffix);
                
                const filledHTML = `<span class="select-none mx-1">` +
                    `<strong class="${colorClass} font-bold">${displayRoot}</strong>` +
                    `<span class="text-slate-800 dark:text-white">${displaySuffix}</span>` +
                    `</span>`;
                    
                const beforeText = sentence.substring(0, match.index);
                const afterText = sentence.substring(match.index + match.length);
                
                document.getElementById('card-front-fillblanks').innerHTML = beforeText + filledHTML + afterText;
            }

            document.getElementById('next-btn').disabled = false;
            document.getElementById('pronounce-btn-front').classList.remove('hidden');
            
            // Auto-pronounce word if enabled (only once per card reveal, after guessing)
            const autoPronounce = localStorage.getItem('greAutoPronounce') === 'true';
            if (autoPronounce && !hasAutoPronouncedThisCard) {
                hasAutoPronouncedThisCard = true;
                pronounceWord();
            }
        }

        function nextWord() {
            if ('speechSynthesis' in window) window.speechSynthesis.cancel();
            if (reviewTossPending) {
                reviewTossPending = false;
                renderCard();
                return;
            }
            if (mode === 'matching') {
                let nextIdx = currentIndex + 1;
                while (nextIdx < appData.length && sessionMatchedIndices.has(nextIdx)) {
                    nextIdx++;
                }
                
                if (nextIdx < appData.length) {
                    currentIndex = nextIdx;
                    if (!isReviewMode && catSelect.value !== 'Random') {
                        const progressKey = `${catSelect.value}|${setSelect.value}`;
                        progressDB[progressKey] = currentIndex;
                        progressDB[progressKey + '_matched'] = Array.from(sessionMatchedIndices);
                        localStorage.setItem('greProgressDB', JSON.stringify(progressDB));
                        hasUnsavedChanges = true;
                    }
                    renderCard();
                } else {
                    if (!isReviewMode && catSelect.value !== 'Random') {
                        const progressKey = `${catSelect.value}|${setSelect.value}`;
                        progressDB[progressKey] = 'COMPLETED'; 
                        delete progressDB[progressKey + '_matched'];
                        localStorage.setItem('greProgressDB', JSON.stringify(progressDB));
                        hasUnsavedChanges = true;
                    }

                    isSessionComplete = true;
                    
                    document.getElementById('card-container-wrapper').classList.remove('hidden');
                    document.getElementById('matching-container').classList.add('hidden');
                    const fillblanksEl = document.getElementById('card-front-fillblanks');
                    fillblanksEl.classList.add('hidden');
                    fillblanksEl.innerHTML = '';
                    document.getElementById('study-screen').classList.remove('fillblanks-mode');
                    
                    const frontText = document.getElementById('card-front-word');
                    frontText.classList.remove('hidden');
                    const frontType = document.getElementById('card-front-type');
                    if (frontType) frontType.classList.add('hidden');
                    const flashcard = document.getElementById('flashcard');
                    
                    frontText.innerText = "🎉 Set Complete!";
                    frontText.classList.remove('text-slate-800', 'dark:text-white', 'capitalize', 'lowercase', 'uppercase');
                    frontText.classList.add('text-emerald-600', 'dark:text-emerald-400', 'normal-case');
                    
                    flashcard.classList.remove('cursor-pointer');
                    flashcard.classList.remove('flipped');
                    
                    document.getElementById('mcq-options').classList.add('hidden');
                    document.getElementById('flashcard-hint').classList.add('hidden');
                    
                    document.getElementById('pronounce-btn-front').classList.add('hidden');
                    document.getElementById('pronounce-btn-back').classList.add('hidden');
                    document.getElementById('example-btn-front').classList.add('hidden');
                    document.getElementById('example-btn-back').classList.add('hidden');
                    document.getElementById('card-front-example').classList.add('hidden');
                    document.getElementById('card-back-example').classList.add('hidden');
                    
                    hideNavControls();
                    document.getElementById('next-btn-container').classList.add('hidden');

                    const countdownContainer = document.getElementById('countdown-container');
                    const countdownBar = document.getElementById('countdown-bar');
                    const cardBottomDeco = document.getElementById('card-bottom-deco');
                    if (cardBottomDeco) cardBottomDeco.classList.add('hidden');
                    if (countdownContainer && countdownBar) {
                        countdownContainer.classList.remove('hidden');
                        countdownBar.style.transition = 'none';
                        countdownBar.style.width = '100%';
                        countdownBar.offsetHeight; // force reflow
                        setTimeout(() => {
                            countdownBar.style.transition = 'width 2.5s linear';
                            countdownBar.style.width = '0%';
                        }, 50);
                    }
                    
                    sessionEndTimeout = setTimeout(() => {
                        endSession();
                        frontText.classList.add('text-slate-800', 'dark:text-white');
                        frontText.classList.remove('text-emerald-600', 'dark:text-emerald-400', 'normal-case');
                        if (cardBottomDeco) cardBottomDeco.classList.remove('hidden');
                        if (countdownContainer && countdownBar) {
                            countdownContainer.classList.add('hidden');
                            countdownBar.style.transition = 'none';
                            countdownBar.style.width = '100%';
                        }
                    }, 2500);
                }

                return;
            }

            // Flashcard, MCQ, or Fill-blanks mode
            // completeWord is only needed for flashcard; MCQ/fillblanks call it in their guess handlers
            if (mode === 'flashcard') {
                completeWord(currentIndex);
            }
            
            let nextIdx;
            if (fillBlanksOrder && !isReviewMode) {
                // Follow the shuffled presentation order for fill-blanks
                // In review mode, skip this branch: splice/push toss operations
                // shift array elements, making fillBlanksOrder indices stale.
                fillBlanksPointer++;
                while (fillBlanksPointer < fillBlanksOrder.length && sessionMatchedIndices.has(fillBlanksOrder[fillBlanksPointer])) {
                    fillBlanksPointer++;
                }
                nextIdx = fillBlanksPointer < fillBlanksOrder.length ? fillBlanksOrder[fillBlanksPointer] : appData.length;
            } else {
                nextIdx = currentIndex + 1;
                while (nextIdx < appData.length && sessionMatchedIndices.has(nextIdx)) {
                    nextIdx++;
                }
            }
            
            if (nextIdx < appData.length) {
                currentIndex = nextIdx;
                renderCard();
            } else {
                if (!isReviewMode && catSelect.value !== 'Random') {
                    const progressKey = `${catSelect.value}|${setSelect.value}`;
                    progressDB[progressKey] = 'COMPLETED'; 
                    delete progressDB[progressKey + '_matched'];
                    localStorage.setItem('greProgressDB', JSON.stringify(progressDB));
                    hasUnsavedChanges = true;
                }

                isSessionComplete = true;
                const fillblanksEl = document.getElementById('card-front-fillblanks');
                fillblanksEl.classList.add('hidden');
                fillblanksEl.innerHTML = '';
                document.getElementById('study-screen').classList.remove('fillblanks-mode');
                const frontText = document.getElementById('card-front-word');
                frontText.classList.remove('hidden');
                const frontType = document.getElementById('card-front-type');
                if (frontType) frontType.classList.add('hidden');
                const flashcard = document.getElementById('flashcard');
                
                frontText.innerText = "🎉 Set Complete!";
                frontText.classList.remove('text-slate-800', 'dark:text-white', 'capitalize', 'lowercase', 'uppercase');
                frontText.classList.add('text-emerald-600', 'dark:text-emerald-400', 'normal-case');
                
                flashcard.classList.remove('cursor-pointer');
                flashcard.classList.remove('flipped');
                
                document.getElementById('mcq-options').classList.add('hidden');
                document.getElementById('flashcard-hint').classList.add('hidden');
                
                document.getElementById('pronounce-btn-front').classList.add('hidden');
                document.getElementById('pronounce-btn-back').classList.add('hidden');
                document.getElementById('example-btn-front').classList.add('hidden');
                document.getElementById('example-btn-back').classList.add('hidden');
                document.getElementById('card-front-example').classList.add('hidden');
                document.getElementById('card-back-example').classList.add('hidden');
                
                // FIX: Hide nav controls properly at end screen
                hideNavControls();
                document.getElementById('next-btn-container').classList.add('hidden');

                // Trigger countdown animation
                const countdownContainer = document.getElementById('countdown-container');
                const countdownBar = document.getElementById('countdown-bar');
                const cardBottomDeco = document.getElementById('card-bottom-deco');
                if (cardBottomDeco) cardBottomDeco.classList.add('hidden');
                if (countdownContainer && countdownBar) {
                    countdownContainer.classList.remove('hidden');
                    countdownBar.style.transition = 'none';
                    countdownBar.style.width = '100%';
                    countdownBar.offsetHeight; // force reflow
                    setTimeout(() => {
                        countdownBar.style.transition = 'width 2.5s linear';
                        countdownBar.style.width = '0%';
                    }, 50);
                }
                
                sessionEndTimeout = setTimeout(() => {
                    endSession();
                    frontText.classList.add('text-slate-800', 'dark:text-white');
                    frontText.classList.remove('text-emerald-600', 'dark:text-emerald-400', 'normal-case');
                    if (cardBottomDeco) cardBottomDeco.classList.remove('hidden');
                    if (countdownContainer && countdownBar) {
                        countdownContainer.classList.add('hidden');
                        countdownBar.style.transition = 'none';
                        countdownBar.style.width = '100%';
                    }
                }, 2500);
            }
        }
        if ('serviceWorker' in navigator) {
            window.addEventListener('load', () => {
                navigator.serviceWorker.register('sw.js').then(registration => {
                    console.log('ServiceWorker registered with scope:', registration.scope);
                }).catch(error => {
                    console.log('ServiceWorker registration failed:', error);
                });
            });
        }

        // Completely block zoom on mobile
        document.addEventListener('touchstart', function(e) {
            if (e.touches.length > 1) e.preventDefault();
        }, { passive: false });

        document.addEventListener('gesturestart', function(e) {
            e.preventDefault();
        }, { passive: false });

        let lastTouchEnd = 0;
        document.addEventListener('touchend', function(e) {
            const now = Date.now();
            if (now - lastTouchEnd <= 300) {
                e.preventDefault();
            }
            lastTouchEnd = now;
        }, { passive: false });

        // Disable iOS swipe-to-go-back gesture
        let touchStartX = 0;
        let touchStartY = 0;

        document.addEventListener('touchstart', function(e) {
            if (e.touches.length === 1) {
                touchStartX = e.touches[0].clientX;
                touchStartY = e.touches[0].clientY;
            }
        }, { passive: true });

        document.addEventListener('touchmove', function(e) {
            if (e.touches.length === 1) {
                const touchX = e.touches[0].clientX;
                const touchY = e.touches[0].clientY;
                const diffX = touchX - touchStartX;
                const diffY = touchY - touchStartY;

                // If the touch started near the left or right edges (within 30px) and is a horizontal swipe
                if ((touchStartX < 30 || touchStartX > window.innerWidth - 30) && Math.abs(diffX) > Math.abs(diffY)) {
                    e.preventDefault();
                }
            }
        }, { passive: false });

        // =========================================================================
        // READING COMPREHENSION QUIZ MODULE
        // =========================================================================

        let activeQuizId = localStorage.getItem('greActiveQuizId') || 'quiz1';

        const passageQuizzes = {
            quiz1: {
                id: 'quiz1',
                title: 'Quiz 1 — Reading Comprehension only',
                subtitle: 'Long Passage & Paragraph Argument (Weaken/Strengthen, Evaluate Argument, Paradox, Assumption)',
                icon: '📖',
                storageKey: 'grePassageProgress'
            },
            quiz2: {
                id: 'quiz2',
                title: 'Quiz 3 — Full Verbal Reasoning',
                subtitle: 'Text Completion, Sentence Equivalence, Reading Comprehension',
                icon: '✍️',
                storageKey: 'grePassageProgress2'
            },
            quiz3: {
                id: 'quiz3',
                title: 'Quiz 2 — Sentence Completion & Equivalence',
                subtitle: 'Text Completion (1, 2, 3 Blanks) & Sentence Equivalence',
                icon: '⚡',
                storageKey: 'grePassageProgress3'
            }
        };

        const passageDataQuiz1 = {
            passageTitle: "Classic Maya Civilization Collapse",
            passageParagraphs: [
                [
                    "The decline of the Classic Maya civilization during the eighth and ninth centuries remains one of archaeology’s most fiercely contested debates, primarily divided between environmental determinists and political theorists.",
                    "For decades, the prevailing consensus favored internal systemic failure—warfare, agricultural degradation, or peasant revolts.",
                    "However, the turn of the twenty-first century witnessed a dramatic paradigm shift, catalyzed by paleoclimatologist Richardson Gill’s sweeping hypothesis that a series of catastrophic megadroughts was the singular, proximate cause of the collapse.",
                    "Gill’s model, relying on sedimentary cores from the Yucatan Peninsula, offers an elegant, if rigid, explanation: without water, the intensely centralized divine kingships simply imploded."
                ],
                [
                    "Yet, treating the Maya collapse as a monolithic event ignores critical geographic and temporal variances.",
                    "Scholars like James Aimers argue that the term \"collapse\" itself is a misnomer, masking a highly nuanced process of regional adaptation and relocation.",
                    "In the northern lowlands, for instance, cities like Chichen Itza actually flourished during the very period the southern centers were being abandoned.",
                    "Aimers’s critique trades the catastrophic for the gradual, suggesting that while drought undoubtedly strained resources, the ultimate dissolution of Classic Maya society was mediated by local political flexibility and trade network resilience.",
                    "To attribute the fall of an entire civilization to a single meteorological anomaly is to reduce complex statecraft to mere ecology."
                ],
                [
                    "A further complication arises from the work of archaeologist David Webster, who suggests that endemic warfare, driven by demographic pressures and elite overproduction, had already hollowed out the institutional stability of the southern lowlands before the severe droughts manifested.",
                    "In Webster’s view, the environmental crises did not initiate the collapse but rather served as the coup de grâce for a system already teetering on the brink of structural insolvency.",
                    "While Gill’s supporters counter that the escalating warfare itself was a direct consequence of resource scarcity induced by early dry spells, this defense risks circular reasoning.",
                    "It leaves unanswered whether the political architecture of the Maya could have withstood the droughts had it not been fundamentally compromised by centuries of unsustainable baseline growth and elite competition.",
                    "Ultimately, the synthesis of these viewpoints suggests that the collapse was not a uniform curtain drop, but an unevenly distributed dissolution wherein environmental pressures acted upon highly variable regional vulnerabilities."
                ]
            ],
            questions: [
                {
                    id: "p_q1",
                    type: "single",
                    passageBased: true,
                    question: "In the context in which it is used, “monolithic” most nearly means",
                    options: ["architectural", "uniform", "ancient", "unyielding", "monumental"],
                    answer: 1,
                    explanation: "The passage contrasts a \"monolithic event\" with \"geographic and temporal variances\" in the very same sentence. It further details how different regions experienced different outcomes (some cities flourished while others were abandoned). Therefore, in this context, \"monolithic\" means uniform or entirely homogenous. (B) is the correct answer."
                },
                {
                    id: "p_q2",
                    type: "single",
                    passageBased: true,
                    question: "The author of the passage would take exception to all of the following statements regarding Gill’s hypothesis EXCEPT?",
                    options: [
                        "Gill’s hypothesis is characterized by a high degree of nuance regarding regional geographic differences.",
                        "Gill's model successfully accounts for the flourishing of northern lowland cities like Chichen Itza.",
                        "The explanatory power of Gill's megadrought theory is uniformly applicable across the entirety of the Yucatan Peninsula.",
                        "Gill's hypothesis offers an explanation that lacks flexibility despite its empirical basis.",
                        "Gill's work completely aligns with the classical twentieth-century consensus on Maya decline."
                    ],
                    answer: 3,
                    explanation: "\"Take exception to\" means to disagree with. Because this is an EXCEPT question, the correct answer is a statement the author would agree with or would not dispute. In the first paragraph, the author calls Gill's hypothesis \"elegant, if rigid,\" indicating that it lacks flexibility despite its reliance on empirical data like sedimentary cores. Therefore, the author agrees with statement (D). The author explicitly disputes or contradicts the assertions made in A, B, C, and E throughout the text."
                },
                {
                    id: "p_q3",
                    type: "multiple",
                    passageBased: true,
                    question: "According to the passage, James Aimers’s view of the Maya decline differs from Richardson Gill’s model in which of the following ways? (Select ALL answers that apply.)",
                    options: [
                        "Aimers emphasizes regional adaptation and relocation rather than a total societal implosion.",
                        "Aimers rejects the premise that environmental factors played any role in the strain on Maya resources.",
                        "Aimers views the phenomenon as a gradual socio-political shift rather than an abrupt, uniform catastrophe."
                    ],
                    answer: [0, 2],
                    explanation: "Statement (A) is correct because the second paragraph explicitly states that Aimers argues the term collapse masks a \"highly nuanced process of regional adaptation and relocation.\"\n\nStatement (B) is incorrect because the text notes that Aimers suggests \"drought undoubtedly strained resources,\" meaning he does not reject the role of environmental factors entirely.\n\nStatement (C) is correct because the text states that Aimers's critique \"trades the catastrophic for the gradual.\" Therefore, both A and C apply."
                },
                {
                    id: "p_q5",
                    type: "single",
                    passageBased: true,
                    question: "It can be inferred from the passage that David Webster would be most likely to agree with which of the following statements?",
                    options: [
                        "Environmental factors were entirely irrelevant to the abandonment of the southern lowland centers.",
                        "Internal socio-political pressures had already compromised Maya institutional stability prior to the worst of the climate crises.",
                        "Elite overproduction was a direct consequence of the megadroughts described by Gill.",
                        "The Maya political system was robust enough to survive structural insolvency if climate conditions had remained stable.",
                        "Southern lowland centers were abandoned primarily due to peasant revolts rather than inter-city warfare."
                    ],
                    answer: 1,
                    explanation: "The third paragraph states that in Webster's view, \"endemic warfare, driven by demographic pressures and elite overproduction, had already hollowed out the institutional stability of the southern lowlands before the severe droughts manifested.\" This directly supports the inference that socio-political pressures compromised stability prior to the climate crisis, making (B) the correct answer."
                },
                {
                    id: "p_q4",
                    type: "sentence",
                    passageBased: true,
                    question: "Select the sentence that identifies a potential logical flaw in the counterargument made by proponents of the environmental explanation.",
                    answer: "While Gill’s supporters counter that the escalating warfare itself was a direct consequence of resource scarcity induced by early dry spells, this defense risks circular reasoning.",
                    explanation: "The third paragraph outlines the debate between David Webster's structural warfare theory and Gill's environmental theory. The selected sentence directly points out that the counterargument offered by Gill's supporters \"risks circular reasoning,\" which is a logical flaw."
                },
                {
                    id: "p_q11",
                    type: "sentence",
                    passageBased: true,
                    question: "Select the sentence that introduces an empirical data source used to support a monocausal theory of the Maya collapse.",
                    answer: "Gill’s model, relying on sedimentary cores from the Yucatan Peninsula, offers an elegant, if rigid, explanation: without water, the intensely centralized divine kingships simply imploded.",
                    explanation: "This sentence mentions \"sedimentary cores\" (the empirical data source) used by Richardson Gill to support his megadrought theory (the monocausal, or single-cause, theory)."
                },
                {
                    id: "p_q12",
                    type: "sentence",
                    passageBased: true,
                    question: "Select the sentence that provides specific historical evidence to challenge the idea of a uniform, civilization-wide decline.",
                    answer: "In the northern lowlands, for instance, cities like Chichen Itza actually flourished during the very period the southern centers were being abandoned.",
                    explanation: "This sentence offers a concrete historical example (Chichen Itza flourishing while the south was abandoned) to prove that the collapse was not uniform or \"monolithic.\""
                },
                {
                    id: "p_q6",
                    type: "single",
                    passageBased: false,
                    prompt: "A major technology corporation has observed a surge in employee complaints regarding digital eye strain. In an effort to curb these symptoms and improve workplace wellness, the company has replaced traditional backlit LCD monitors with reflective e-ink displays across its primary corporate offices. The company's executive board predicts that the number of eye strain complaints will significantly decrease over the next quarter following this installation.",
                    promptLabel: "PARAGRAPH ARGUMENT — STRENGTHEN",
                    question: "Which of the following, if true, most strengthens the validity of the conclusion?",
                    options: [
                        "Most employees at the company use their workstations for greater than six hours per day.",
                        "Reflective e-ink displays emit significantly less high-energy blue light, which clinical studies have directly linked to corporate eye strain complaints.",
                        "The capital expense required to procure e-ink displays is higher than that of maintaining traditional LCD monitors.",
                        "Employees who wore corrective prescription lenses reported no changes in visual comfort during a brief pre-installation trial phase.",
                        "Other corporations that introduced ergonomic keyboard setups saw a minor decrease in repetitive strain injuries."
                    ],
                    answer: 1,
                    explanation: "The argument assumes a causal link between installing e-ink displays and reducing eye strain complaints. (B) strengthens the argument by providing the missing empirical link: it explains why e-ink displays would reduce strain (by eliminating high-energy blue light, a proven cause of the complaints). This validates the board's prediction."
                },
                {
                    id: "p_q7",
                    type: "single",
                    passageBased: false,
                    prompt: "Organic produce at Meadowbrook Farms grocery store costs roughly 30 percent more than conventional produce of the exact same variety. A consumer advocacy group claims that the grocery franchise is simply taking advantage of its reputation for health-conscious options to reap artificially higher profit margins on those organic items.",
                    promptLabel: "PARAGRAPH ARGUMENT — EVALUATE",
                    question: "In evaluating the argument, it would be most useful to compare",
                    options: [
                        "the nutritional and vitamin content of the organic produce with that of the conventional produce at Meadowbrook Farms.",
                        "the wholesale procurement, handling, and farming overhead costs of organic produce with the comparable costs for conventional produce.",
                        "the average household income of consumers who shop at Meadowbrook Farms with the national average household income.",
                        "the sales volume of conventional produce at Meadowbrook Farms with the sales volume of conventional produce at competing grocery chains.",
                        "the percentage of profit derived from organic vegetables versus organic fruits within Meadowbrook Farms stores."
                    ],
                    answer: 1,
                    explanation: "The consumer group claims that the higher price is purely due to price gouging (\"exploiting its reputation\"). To evaluate this claim, we must check if there is an alternative, valid reason for the higher price—such as higher production or operating costs. (B) allows us to make this comparison. If organic items cost 30 percent more to procure and handle, the store isn't necessarily exploiting anyone; if the overhead costs are identical, the group's argument is highly strengthened."
                },
                {
                    id: "p_q8",
                    type: "single",
                    passageBased: false,
                    prompt: "Economist: To revitalize the manufacturing sector in the province of Oakhaven, the regional government should provide tax credits exclusively to firms that construct automated robotics factories. While this policy targets a highly specific sub-sector, the resulting industrial ecosystem will make Oakhaven more economically resilient than any other province. This is not to say that tax credits should be distributed to all technology firms. Rather, only to those directly manufacturing industrial robotics.",
                    promptLabel: "PARAGRAPH ARGUMENT — ASSUMPTION",
                    question: "The conclusion drawn above depends on which of the following assumptions?",
                    options: [
                        "Traditional manufacturing sub-sectors, such as textiles and steel, are completely incapable of experiencing job growth.",
                        "Oakhaven currently possesses a significantly higher unemployment rate than neighboring provinces.",
                        "Industrial robotics manufacturing capability is the primary indicator and driver of a province's long-term economic resilience.",
                        "It is impossible for automated robotics factories to operate successfully without relying heavily on imported raw materials.",
                        "The tax revenue lost from these targeted credits will be instantly offset by corporate property taxes within two fiscal years."
                    ],
                    answer: 2,
                    explanation: "The economist concludes that subsidizing this single, specific sub-sector will make Oakhaven \"more economically resilient than any other province.\" For this to hold true, the economist must assume that industrial robotics is the central, defining factor in economic resilience. If something else matters more, or if robotics doesn't drive resilience, the argument fails. This directly points to (C)."
                },
                {
                    id: "p_q9",
                    type: "single",
                    passageBased: false,
                    prompt: "In a certain territory, over 75 percent of households own a personal vehicle, but historically, premium comprehensive vehicle insurance policies have sold poorly in this region. The percentage of land and population devoted to car ownership is not expected to change, and the average traffic accident rate has slowly risen over the past decade. Despite this trend, a new international insurance firm is building a large headquarters in the territory, and its business plan for success depends on strong local sales of its premium insurance plans. Both the firm's executives and industry analysts expect this venture to be highly profitable over the next few years.",
                    promptLabel: "PARAGRAPH ARGUMENT — PARADOX",
                    question: "Which of the following, if true, most helps to provide a justification for the firm's and the analysts' optimistic expectations?",
                    options: [
                        "The average cost of medical care and vehicle replacement parts has spiked drastically, making basic legal-minimum liability coverage insufficient to protect drivers from catastrophic financial ruin.",
                        "The new insurance firm plans to launch an aggressive marketing campaign focused on sponsoring major professional sporting events in the capital.",
                        "The regional government recently voted to decrease the mandatory minimum liability coverage required for registered drivers.",
                        "Premium insurance policies offer a wider variety of digital customer service hotlines than standard or basic insurance policies do.",
                        "Many citizens prefer to use public transit networks during peak weekend traffic hours rather than driving their personal vehicles."
                    ],
                    answer: 0,
                    explanation: "The paradox is that premium insurance historically sells poorly and accident rates are rising, yet analysts expect a new premium insurance company to thrive on local sales. (A) resolves the paradox by explaining why consumer behavior is about to change: basic insurance is no longer sufficient due to skyrocketing medical and repair costs, forcing drivers to upgrade to premium plans to avoid financial ruin."
                },
                {
                    id: "p_q10",
                    type: "single",
                    passageBased: false,
                    prompt: "A municipal transit authority observed that city bus ridership declined by 15 percent immediately after they implemented a 50-cent fare increase. In an effort to restore ridership to its previous historical levels, the authority plans to lower fares back to their original rate next month, concluding that this price reduction will bring back all the lost passengers.",
                    promptLabel: "PARAGRAPH ARGUMENT — WEAKEN",
                    question: "Which of the following, if true, most seriously weakens the validity of the conclusion?",
                    options: [
                        "The temporary fare increase successfully allowed the transit authority to balance its structural budget deficit for the fiscal year.",
                        "During the period of the fare increase, a new subterranean light rail network opened along identical transit routes, permanently drawing commuter habits away from the bus system.",
                        "A small percentage of city residents rely on the bus system daily regardless of fluctuations in the fare price.",
                        "The transit authority did not aggressively publicize the initial fare increase before it went into effect last year.",
                        "Neighboring municipalities charge higher average transit fares than this city does."
                    ],
                    answer: 1,
                    explanation: "The transit authority assumes that price was the only reason ridership dropped and that reversing the price change will reverse the effect. (B) introduces an alternative, permanent cause for the drop in ridership: the opening of a competing light rail network. If commuters have permanently switched to the light rail, simply lowering bus fares will not bring them back, severely weakening the authority's conclusion."
                }
            ]
        };

        const passageDataQuiz2 = {
            passageTitle: "Historical Linguistics & Population Migration",
            passageParagraphs: [
                [
                    "For decades, historical linguists operated under the structuralist assumption that language evolution is primarily an internal, self-contained mechanism driven by phonetic drift and grammaticalization.",
                    "This view posits that languages change over generations as speakers naturally streamline complex pronunciations or repurpose lexical items into structural markers, entirely independent of external societal disruptions.",
                    "However, recent sociolinguistic frameworks have challenged this insular paradigm, arguing instead that large-scale linguistic shifts are intrinsically bound to demic diffusion\u2014the physical migration of human populations\u2014and cultural contact.",
                    "By cross-referencing phylogenetic language trees with ancient DNA (aDNA) analysis, researchers have demonstrated that the expansion of the Indo-European language family closely correlates with the pastoralist migrations of the Yamnaya culture from the Pontic-Caspian steppe during the Early Bronze Age.",
                    "This interdisciplinary synthesis suggests that linguistic maps cannot be decoupled from demographic history.",
                    "Critics of this contact-driven model caution against an over-reliance on genetic data, arguing that language can diffuse across static populations through trade networks and elite dominance without substantial genetic turnover, as seen in the historical spread of Latin across Western Europe.",
                    "Nonetheless, the integration of biomolecular archaeology has fundamentally destabilized the notion of language as a pristine, closed system evolving in an environmental vacuum."
                ]
            ],
            questions: [
                {
                    id: "v2_q1",
                    type: "single",
                    passageBased: false,
                    prompt: "Given the absolute lack of empirical evidence supporting the claim, the committee\u2019s decision to greenlight the multi-million dollar expansion project was viewed by many as entirely _______.",
                    promptLabel: "TEXT COMPLETION",
                    question: "Select the word that best completes the sentence.",
                    options: ["judicious", "capricious", "inevitable", "verified", "customary"],
                    answer: 1,
                    explanation: "The sentence contrasts the action (greenlighting a huge project) with the basis for it (absolute lack of empirical evidence). Acting without evidence means the decision was arbitrary or impulsive. \"Capricious\" perfectly captures this.\n\nWhy the others fail: \"Judicious\" (wise) and \"verified\" (proven) contradict the lack of evidence. \"Inevitable\" (unavoidable) and \"customary\" (traditional) are unsupported."
                },
                {
                    id: "v2_q2",
                    type: "two_blank",
                    passageBased: false,
                    prompt: "Although the professor’s lectures were initially criticized for being excessively (i)_______, careful review of his course syllabus revealed a surprisingly (ii)_______ underlying structure that unified the seemingly disparate topics.",
                    promptLabel: "TEXT COMPLETION",
                    question: "Select one entry for each blank from the corresponding column of choices.",
                    blanks: [
                        { label: "Blank (i)", options: ["disjointed", "rigorous", "pedantic"] },
                        { label: "Blank (ii)", options: ["convoluted", "coherent", "redundant"] }
                    ],
                    answer: [0, 1],
                    explanation: "\"Although\" signals contrast between the two blanks. The second half mentions the structure \"unified\" topics that were \"seemingly disparate.\" The initial criticism (Blank i) must mean scattered → disjointed. The contrast backed by \"unified\" means the structure was well-organized → coherent."
                },
                {
                    id: "v2_q3",
                    type: "three_blank",
                    passageBased: false,
                    prompt: "Early internet pioneers envisioned a decentralized digital landscape that would (i)_______ traditional institutional gatekeepers; however, the contemporary reality features an unprecedented consolidation of power by a handful of tech conglomerates, a development that many critics find profoundly (ii)_______ and completely at odds with the network’s original (iii)_______ ethos.",
                    promptLabel: "TEXT COMPLETION",
                    question: "Select one entry for each blank from the corresponding column of choices.",
                    blanks: [
                        { label: "Blank (i)", options: ["bypass", "entrench", "scrutinize"] },
                        { label: "Blank (ii)", options: ["encouraging", "alarming", "predictable"] },
                        { label: "Blank (iii)", options: ["hierarchical", "mercantilist", "egalitarian"] }
                    ],
                    answer: [0, 1, 2],
                    explanation: "Blank (i): A \"decentralized\" landscape would avoid \"traditional gatekeepers\" → bypass.\n\nBlank (ii): \"However\" contrasts with \"unprecedented consolidation of power.\" Critics view this negatively → alarming.\n\nBlank (iii): The \"original ethos\" of a decentralized, distributed system → egalitarian (the belief that all people are equally important, possess equal fundamental worth, and should have the same rights, privileges, and opportunities in life)."
                },
                {
                    id: "v2_q4",
                    type: "sentence_equiv",
                    passageBased: false,
                    prompt: "Despite the CEO\u2019s efforts to project an aura of total transparency, her cryptic responses during the investigative press conference only served to _______ the truth behind the company\u2019s sudden financial insolvency.",
                    promptLabel: "SENTENCE EQUIVALENCE",
                    question: "Select the TWO answer choices that produce sentences most alike in meaning.",
                    options: ["illuminate", "obfuscate", "complicate", "clarify", "expedite", "cloud"],
                    answer: [1, 5],
                    explanation: "\"Despite\" signals contrast between the CEO's goal (\"total transparency\") and the outcome. Her \"cryptic\" responses hid the truth. Both \"obfuscate\" and \"cloud\" mean to make obscure.\n\nWhy the others fail: \"Illuminate\" and \"clarify\" mean the opposite. \"Complicate\" doesn't form a synonym pair with another choice."
                },
                {
                    id: "v2_q5",
                    type: "sentence_equiv",
                    passageBased: false,
                    prompt: "The ancient stone artifact discovered at the remote archaeological site was remarkably _______; it possessed no identifying markers, distinctive tool markings, or structural degradation that could definitively link it to any known regional civilization of that era.",
                    promptLabel: "SENTENCE EQUIVALENCE",
                    question: "Select the TWO answer choices that produce sentences most alike in meaning.",
                    options: ["pristine", "anomalous", "singular", "commonplace", "enigmatic", "inscrutable"],
                    answer: [4, 5],
                    explanation: "The artifact has \"no identifying markers\" and cannot be linked to \"any known regional civilization.\" It is deeply mysterious. Both \"enigmatic\" and \"inscrutable\" mean mysterious or impossible to interpret.\n\nWhy the others fail: \"Pristine\" means clean/unspoiled. \"Anomalous\" and \"singular\" don't match the clue about lack of interpretive data."
                },
                {
                    id: "v2_q6",
                    type: "single",
                    passageBased: true,
                    question: "The primary purpose of the passage is to",
                    options: [
                        "defend a traditional structuralist model of language evolution against recent empirical criticisms.",
                        "discuss how recent interdisciplinary research has challenged a long-held view of how languages change.",
                        "argue that genetic data provides a more reliable metric for mapping language families than phonetic analysis.",
                        "demonstrate that the spread of Latin in Western Europe is an exception to an otherwise universal linguistic rule.",
                        "reconcile two competing theories regarding the migration patterns of Bronze Age pastoralists."
                    ],
                    answer: 1,
                    explanation: "The passage opens with a long-held view (structuralist assumption), introduces a challenge (\"However, recent sociolinguistic frameworks...\"), provides interdisciplinary evidence, presents counter-arguments, and concludes the old framework is destabilized. This matches (B).\n\nWhy the others fail: (A) is the opposite. (C) goes too far. (D) treats a counter-example as the main purpose. (E) misidentifies the core topic."
                },
                {
                    id: "v2_q7",
                    type: "multiple",
                    passageBased: true,
                    question: "According to the passage, critics of the contact-driven model argue that language spread can occur through which mechanisms without requiring significant population migration? (Select ALL that apply.)",
                    options: [
                        "Commercial exchange systems",
                        "The political or social influence of ruling classes",
                        "Natural internal phonetic drift over generations"
                    ],
                    answer: [0, 1],
                    explanation: "The passage states critics argue language can diffuse through \"trade networks and elite dominance without substantial genetic turnover.\"\n\n(A) is correct: \"trade networks\" = commercial exchange systems.\n(B) is correct: \"elite dominance\" = political/social influence of ruling classes.\n(C) is incorrect: \"phonetic drift\" is part of the structuralist model, not the critics' argument."
                },
                {
                    id: "v2_q8",
                    type: "sentence",
                    passageBased: true,
                    question: "Select the sentence that introduces a specific historical example used by critics to contest the idea that language expansion always requires genetic or population turnover.",
                    answer: "Critics of this contact-driven model caution against an over-reliance on genetic data, arguing that language can diffuse across static populations through trade networks and elite dominance without substantial genetic turnover, as seen in the historical spread of Latin across Western Europe.",
                    explanation: "This is the only sentence where the critics' counter-argument is paired with a concrete historical example: \"the historical spread of Latin across Western Europe.\""
                },
                {
                    id: "v2_q9",
                    type: "single",
                    passageBased: false,
                    prompt: "A marine biology institute observed a sharp decline in the health of coral reefs near a coastal tourist town. The researchers hypothesized that the primary culprit was the chemical oxybenzone, a common ingredient in commercial sunscreens used by tourists. To test this, the local town council banned all sunscreens containing oxybenzone starting exactly one year ago. Over the past twelve months, the rate of coral bleaching in the area decreased by 40 percent. The council concluded that the ban on oxybenzone sunscreens was directly responsible for the recovery of the coral reef.",
                    promptLabel: "PARAGRAPH ARGUMENT \u2014 STRENGTHEN",
                    question: "Which of the following, if true, most strengthens the validity of the council\u2019s conclusion?",
                    options: [
                        "The total number of tourists visiting the coastal town\u2019s beaches increased by 15 percent over the past year.",
                        "Local water temperatures, which are known to induce massive coral bleaching when unusually high, remained at historically normal, stable levels during the past year.",
                        "A neighboring coastal town that did not ban oxybenzone saw a minor increase in its own coral bleaching rates over the same twelve-month period.",
                        "Most tourists complied with the ban by purchasing alternative sunscreens that use zinc oxide or titanium dioxide as UV filters.",
                        "The local coral reef is home to several endangered species of marine life that rely on healthy coral structures for survival."
                    ],
                    answer: 1,
                    explanation: "The argument claims removing oxybenzone caused the reef\u2019s recovery. (B) strengthens this by ruling out a confounding cause: water temperatures were stable and normal. This makes the sunscreen ban more likely the true cause.\n\nWhy the others fail: (A) doesn\u2019t isolate the chemical variable. (C) is correlational from another location. (D) shows compliance but not causation. (E) is irrelevant to causal logic."
                },
                {
                    id: "v2_q10",
                    type: "single",
                    passageBased: false,
                    prompt: "A city manager noticed that traffic congestion at a major downtown intersection dropped significantly after a new synchronized smart-light system was installed. Seeking to reduce congestion across the entire city, the manager plans to install the identical smart-light system at all remaining intersections next month, concluding that this citywide rollout will replicate the initial reduction in traffic delays.",
                    promptLabel: "PARAGRAPH ARGUMENT \u2014 WEAKEN",
                    question: "Which of the following, if true, most seriously weakens the city manager\u2019s conclusion?",
                    options: [
                        "The smart-light system costs twice as much to maintain annually as traditional timed traffic signals.",
                        "The downtown intersection features highly predictable, uniform commuter traffic, whereas the remaining city intersections experience highly erratic and unpredictable traffic fluxes that the system\u2019s algorithm cannot process in real time.",
                        "Several major road construction projects near the downtown intersection were completed right before the smart lights were installed, reopening two previously blocked lanes.",
                        "Some drivers reported initial confusion when interacting with the newly timed lights during the first week of implementation.",
                        "The software powering the smart-light system requires monthly data updates to account for seasonal daylight shifts."
                    ],
                    answer: 1,
                    explanation: "The manager assumes what worked for one intersection will work everywhere. (B) shows other intersections have fundamentally different traffic patterns the algorithm can\u2019t handle.\n\nWhy the others fail: (A) is about cost, not effectiveness. (C) explains the first intersection\u2019s success but doesn\u2019t undermine deployment to others as effectively."
                },
                {
                    id: "v2_q11",
                    type: "single",
                    passageBased: false,
                    prompt: "Agricultural analysts observe that switching from traditional soil-based farming to vertical hydroponic indoor farming reduces water usage by 90 percent per acre of crops produced. Therefore, the analysts conclude that if the nation\u2019s agricultural sector transitions entirely to vertical indoor farming, the total amount of water consumed by the nation annually will decrease significantly.",
                    promptLabel: "PARAGRAPH ARGUMENT \u2014 ASSUMPTION",
                    question: "The conclusion drawn by the analysts depends on which of the following assumptions?",
                    options: [
                        "Vertical indoor farming produces crops that are nutritionally superior to traditionally grown crops.",
                        "The energy required to power the artificial lighting in vertical farms will not create a substantial carbon footprint.",
                        "The agricultural sector is currently responsible for a meaningful percentage of the nation\u2019s total annual water consumption.",
                        "The cost of constructing indoor vertical farming facilities will decrease as the technology becomes more widely adopted.",
                        "Mainstream consumers will be willing to pay slightly higher prices for produce grown via hydroponic methods."
                    ],
                    answer: 2,
                    explanation: "The argument jumps from a percentage reduction within farming to a massive reduction in national water use. For this to hold, farming must make up a significant portion of national water use. If agriculture only used 0.05% of national water, a 90% drop would change nothing nationally. (C) is a necessary assumption.\n\nWhy the others fail: Nutrition (A), carbon (B), cost (D), and consumer willingness (E) don\u2019t impact the core mathematical logic."
                },
                {
                    id: "v2_q12",
                    type: "single",
                    passageBased: false,
                    prompt: "A premium subscription-based streaming service recently increased its monthly fee by 25 percent. Historically, price hikes of this magnitude within the digital media industry have led to an immediate, sharp wave of subscription cancellations. However, three months after this price increase went into effect, the streaming service reported not only a record-high total number of active subscribers but also its lowest cancellation rate in five years, despite releasing no new high-profile exclusive content during this period.",
                    promptLabel: "PARAGRAPH ARGUMENT \u2014 PARADOX",
                    question: "Which of the following, if true, most helps to resolve the apparent discrepancy described above?",
                    options: [
                        "The streaming service spent less money on marketing and advertising during the quarter in which the price hike occurred.",
                        "Two major competing streaming platforms unexpectedly shut down their services permanently a week before the price hike took effect.",
                        "Customer surveys indicate that current subscribers value high-definition video streaming quality over low cost.",
                        "The streaming service\u2019s customer service department implemented a new automated chatbot to handle account billing questions.",
                        "The 25 percent price increase was accompanied by a minor aesthetic restructuring of the platform\u2019s mobile application user interface."
                    ],
                    answer: 1,
                    explanation: "The paradox: Why did a massive price hike lead to more subscribers and fewer cancellations? (B) explains this: two major competitors shut down, flooding this platform with displaced users who had nowhere else to go.\n\nWhy the others fail: Less marketing (A) would decrease acquisition. Preferences (C) don\u2019t explain a sudden increase. Chatbots (D) and UI updates (E) are too minor."
                }
            ]
        };

        const passageDataQuiz3 = {
            passageTitle: "Sentence Completion & Equivalence",
            passageParagraphs: [],
            questions: [
                {
                    id: "v3_q1",
                    type: "single",
                    passageBased: false,
                    prompt: "The author's latest novel was criticized for its _______ structure; events did not follow a chronological sequence, instead jumping erratically between different centuries and characters with no apparent transition.",
                    promptLabel: "TEXT COMPLETION",
                    question: "Select the word that best completes the sentence.",
                    options: ["linear", "convoluted", "digressive", "fragmented", "uniform"],
                    answer: 3,
                    explanation: "The clue is 'did not follow a chronological sequence, instead jumping erratically...'. This suggests a structure that is broken up or disjointed. 'Fragmented' is the best choice. 'Convoluted' means extremely complex, but 'fragmented' directly matches the jumping/broken nature of the timeline. 'Linear' is the opposite, 'digressive' means departing from the main subject, and 'uniform' means identical or homogeneous."
                },
                {
                    id: "v3_q2",
                    type: "single",
                    passageBased: false,
                    prompt: "Despite his reputation for being exceptionally _______ in public debates, the politician was surprisingly reticent and reserved when speaking in private circles.",
                    promptLabel: "TEXT COMPLETION",
                    question: "Select the word that best completes the sentence.",
                    options: ["taciturn", "garrulous", "imperious", "diffident", "laconic"],
                    answer: 1,
                    explanation: "The word 'Despite' indicates a contrast between the politician's public behavior and his private behavior ('reticent and reserved'). Reticent and reserved means quiet and disinclined to speak. The opposite of this is talkative or wordy. 'Garrulous' means excessively talkative, which perfectly fits the contrast. 'Taciturn' and 'laconic' are synonyms for reticent, 'diffident' means shy/lacking self-confidence, and 'imperious' means domineering."
                },
                {
                    id: "v3_q3",
                    type: "two_blank",
                    passageBased: false,
                    prompt: "Because the initial results of the clinical trial were highly (i)_______, the researchers cautioned that it would be (ii)_______ to draw any definitive conclusions about the drug's efficacy until larger cohorts had been tested.",
                    promptLabel: "TEXT COMPLETION",
                    question: "Select one entry for each blank from the corresponding column of choices.",
                    blanks: [
                        { label: "Blank (i)", options: ["irrefutable", "salutary", "equivocal"] },
                        { label: "Blank (ii)", options: ["premature", "judicious", "superfluous"] }
                    ],
                    answer: [2, 0],
                    explanation: "The first blank must reflect a quality that leads the researchers to caution against drawing definitive conclusions. 'Equivocal' (open to more than one interpretation; ambiguous or undecided) fits well. Since the results are equivocal, drawing definitive conclusions before testing larger groups would be too early or unwise, making 'premature' the correct fit for the second blank. 'Salutary' means beneficial, 'irrefutable' means impossible to deny, and 'judicious' means wise."
                },
                {
                    id: "v3_q4",
                    type: "two_blank",
                    passageBased: false,
                    prompt: "While some art historians argue that the painter's early works were merely (i)_______ imitations of Renaissance masters, others detect a subtle subversion of classical conventions that foreshadowed the artist's later, highly (ii)_______ style.",
                    promptLabel: "TEXT COMPLETION",
                    question: "Select one entry for each blank from the corresponding column of choices.",
                    blanks: [
                        { label: "Blank (i)", options: ["idiosyncratic", "slavish", "novice"] },
                        { label: "Blank (ii)", options: ["derivative", "monotonous", "revolutionary"] }
                    ],
                    answer: [1, 2],
                    explanation: "The first blank describes 'imitations of Renaissance masters'. The contrast is signaled by 'others detect a subtle subversion... that foreshadowed the artist's later...' which means the first group saw them as unoriginal or blindly copying. 'Slavish' means showing no originality or blindly copying. For the second blank, the later style is contrasted with these early imitative works and characterized by 'subversion of classical conventions', indicating it is highly original or 'revolutionary'."
                },
                {
                    id: "v3_q5",
                    type: "three_blank",
                    passageBased: false,
                    prompt: "Though science journalists often portray scientific breakthroughs as (i)_______ events arising from sudden flashes of genius, the reality of academic research is far more (ii)_______, requiring decades of incremental progress, trial and error, and (iii)_______ collaboration.",
                    promptLabel: "TEXT COMPLETION",
                    question: "Select one entry for each blank from the corresponding column of choices.",
                    blanks: [
                        { label: "Blank (i)", options: ["fortuitous", "gradual", "monolithic"] },
                        { label: "Blank (ii)", options: ["unremarkable", "capricious", "laborious"] },
                        { label: "Blank (iii)", options: ["intermittent", "sustained", "peripheral"] }
                    ],
                    answer: [0, 2, 1],
                    explanation: "Blank (i): The prompt contrasts the portrayal of breakthroughs ('sudden flashes of genius') with the actual reality. 'Fortuitous' (happening by chance/accident rather than design, i.e., luck/inspiration) fits best. Blank (ii): The reality is described as requiring 'decades of incremental progress'. This means it is highly demanding and hard work, making 'laborious' the correct choice. Blank (iii): The collaboration needed over decades must be continuous and ongoing, which is described as 'sustained'."
                },
                {
                    id: "v3_q6",
                    type: "three_blank",
                    passageBased: false,
                    prompt: "A society that (i)_______ intellectual dissent and demands absolute conformity eventually suffers from cultural (ii)_______, as the lack of novel ideas prevents the social adaptation necessary to survive in a (iii)_______ global landscape.",
                    promptLabel: "TEXT COMPLETION",
                    question: "Select one entry for each blank from the corresponding column of choices.",
                    blanks: [
                        { label: "Blank (i)", options: ["fosters", "stifles", "tolerates"] },
                        { label: "Blank (ii)", options: ["stagnation", "vitality", "exuberance"] },
                        { label: "Blank (iii)", options: ["static", "homogeneous", "fluid"] }
                    ],
                    answer: [1, 0, 2],
                    explanation: "Blank (i): Demanding absolute conformity means the society suppresses or cracks down on dissent, so it 'stifles' it. Blank (ii): Stifling dissent and having a 'lack of novel ideas' leads to a state of inactive decay or 'stagnation'. Blank (iii): To survive, the society must adapt. This adaptation is needed because the global landscape is constantly changing, dynamic, or 'fluid'."
                },
                {
                    id: "v3_q7",
                    type: "sentence_equiv",
                    passageBased: false,
                    prompt: "The research team’s conclusions were initially met with skepticism, but they were eventually vindicated by a series of _______ experiments conducted by independent laboratories.",
                    promptLabel: "SENTENCE EQUIVALENCE",
                    question: "Select the TWO answer choices that produce sentences most alike in meaning.",
                    options: ["corroborative", "flawed", "dubious", "supporting", "speculative", "innovative"],
                    answer: [0, 3],
                    explanation: "The sentence says the team's conclusions were 'eventually vindicated' (proven correct or justified). This means the experiments conducted by other labs must have confirmed their results. Both 'corroborative' and 'supporting' mean to confirm or give support to a statement or theory. 'Flawed' and 'dubious' are negative, 'speculative' means theoretical, and 'innovative' means introducing new ideas."
                },
                {
                    id: "v3_q8",
                    type: "sentence_equiv",
                    passageBased: false,
                    prompt: "Despite the company's public assurances that the reorganization would be painless, many employees remain _______ about their future job security.",
                    promptLabel: "SENTENCE EQUIVALENCE",
                    question: "Select the TWO answer choices that produce sentences most alike in meaning.",
                    options: ["sanguine", "aphetic", "apprehensive", "indifferent", "fearful", "complacent"],
                    answer: [2, 4],
                    explanation: "The word 'Despite' indicates a contrast between the company's positive assurances ('painless') and the employees' actual feelings about job security. They would be worried or anxious. 'Apprehensive' and 'fearful' both mean anxious or fearful about the future. 'Sanguine' means optimistic (the opposite), 'indifferent' means unconcerned, and 'complacent' means self-satisfied."
                },
                {
                    id: "v3_q9",
                    type: "sentence_equiv",
                    passageBased: false,
                    prompt: "The diplomat's speeches were renowned for their _______ nature, often leaving foreign ministers struggling to determine his country's true policy positions.",
                    promptLabel: "SENTENCE EQUIVALENCE",
                    question: "Select the TWO answer choices that produce sentences most alike in meaning.",
                    options: ["lucid", "equivocal", "forthright", "candid", "ambiguous", "turgid"],
                    answer: [1, 4],
                    explanation: "The clue is 'leaving foreign ministers struggling to determine his country's true policy positions'. This indicates that his speeches were unclear, vague, or had double meanings. Both 'equivocal' and 'ambiguous' mean open to more than one interpretation or vague. 'Lucid', 'forthright', and 'candid' all imply clarity or honesty, which is the opposite of the clue."
                },
                {
                    id: "v3_q10",
                    type: "sentence_equiv",
                    passageBased: false,
                    prompt: "Because the ecosystem is highly fragile, even a _______ disruption in the food chain can trigger a cascading ecological collapse across the entire region.",
                    promptLabel: "SENTENCE EQUIVALENCE",
                    question: "Select the TWO answer choices that produce sentences most alike in meaning.",
                    options: ["catastrophic", "minor", "trivial", "substantial", "profound", "systemic"],
                    answer: [1, 2],
                    explanation: "The sentence uses the logic of 'highly fragile', which means that it doesn't take much to disrupt it. Even a small or insignificant disruption can cause a massive ('cascading') collapse. Both 'minor' and 'trivial' mean small or insignificant. 'Catastrophic', 'substantial', and 'profound' would describe a large disruption, which doesn't emphasize the fragility of the ecosystem as effectively."
                },
                {
                    id: "v3_q11",
                    type: "sentence_equiv",
                    passageBased: false,
                    prompt: "For decades, the professor’s monographs were considered the _______ authority on early Byzantine art, cited by nearly every major scholar in the field.",
                    promptLabel: "SENTENCE EQUIVALENCE",
                    question: "Select the TWO answer choices that produce sentences most alike in meaning.",
                    options: ["definitive", "tenuous", "peripheral", "classical", "canonical", "negligible"],
                    answer: [0, 4],
                    explanation: "The clue is 'cited by nearly every major scholar in the field'. This means the monographs were seen as the standard, authoritative, or accepted works. Both 'definitive' and 'canonical' mean authoritative, standard, or accepted as rule/fact in a field of study. 'Tenuous' means weak, 'peripheral' means marginal/outer, and 'negligible' means insignificant."
                },
                {
                    id: "v3_q12",
                    type: "sentence_equiv",
                    passageBased: false,
                    prompt: "The modern software developer must avoid the trap of writing _______ code, which may function correctly under ideal circumstances but breaks down when faced with unexpected inputs or network latency.",
                    promptLabel: "SENTENCE EQUIVALENCE",
                    question: "Select the TWO answer choices that produce sentences most alike in meaning.",
                    options: ["robust", "brittle", "fragile", "efficient", "redundant", "obfuscated"],
                    answer: [1, 2],
                    explanation: "The clue describes code that 'breaks down when faced with unexpected inputs or network latency'. This means the code is easily broken or delicate. Both 'brittle' and 'fragile' describe something that is easily broken, damaged, or fails under stress. 'Robust' means strong and resilient (the opposite), 'efficient' means performing well, and 'redundant' means superfluous."
                }
            ]
        };

        let passageData = activeQuizId === 'quiz3' ? passageDataQuiz3 : (activeQuizId === 'quiz2' ? passageDataQuiz2 : passageDataQuiz1);

        function switchActiveQuiz(quizId) {
            activeQuizId = quizId;
            localStorage.setItem('greActiveQuizId', quizId);
            passageData = quizId === 'quiz3' ? passageDataQuiz3 : (quizId === 'quiz2' ? passageDataQuiz2 : passageDataQuiz1);
        }

        let passageState = {
            currentIdx: 0,
            answers: {},
            submitted: {},
            correctness: {}
        };
        let selectedSentencePos = null;

        function loadPassageState() {
            const saved = localStorage.getItem(passageQuizzes[activeQuizId].storageKey);
            if (saved) {
                try {
                    passageState = JSON.parse(saved);
                } catch(e) {
                    console.error("Error loading passage state", e);
                }
            } else {
                resetPassageStateNoConfirm();
            }
        }

        function savePassageState() {
            localStorage.setItem(passageQuizzes[activeQuizId].storageKey, JSON.stringify(passageState));
        }

        function resetPassageStateNoConfirm() {
            passageState = {
                currentIdx: 0,
                answers: {},
                submitted: {},
                correctness: {}
            };
            selectedSentencePos = null;
            savePassageState();
        }

        function isPassageQuizComplete() {
            return passageData.questions.every(q => passageState.submitted[q.id]);
        }

        function goToPassageMode() {
            // If already in passage-screen, open the quiz selector instead of going back to main menu
            const activeScreen = _navStack[_navStack.length - 1];
            if (activeScreen === 'passage-screen') {
                showQuizSelector();
                return;
            }

            if (_navStack.includes('study-screen') && !confirm('Leave your current study session and open Reading & Reasoning? Progress will be saved.')) {
                return;
            }
            _navStack = ['setup-screen', 'passage-screen'];
            _showScreen('passage-screen');
            showQuizSelector();
        }

        function showQuizSelector() {
            document.getElementById('passage-quiz-container').classList.add('hidden');
            document.getElementById('passage-quiz-container').classList.remove('flex');
            document.getElementById('passage-results-container').classList.add('hidden');
            document.getElementById('passage-quiz-selector').classList.remove('hidden');
            document.getElementById('passage-reset-btn').classList.add('hidden');
            
            const titleEl = document.getElementById('passage-main-title');
            const subtitleEl = document.getElementById('passage-subtitle');
            if (titleEl) titleEl.innerText = "Reading & Reasoning";
            if (subtitleEl) subtitleEl.innerText = "GRE Reading Comprehension";
            
            ['quiz1', 'quiz2', 'quiz3'].forEach(qId => {
                const meta = passageQuizzes[qId];
                const data = qId === 'quiz3' ? passageDataQuiz3 : (qId === 'quiz2' ? passageDataQuiz2 : passageDataQuiz1);
                const saved = localStorage.getItem(meta.storageKey);
                let progress = 0, correct = 0, total = data.questions.length;
                if (saved) {
                    try {
                        const st = JSON.parse(saved);
                        progress = Object.keys(st.submitted || {}).filter(k => st.submitted[k]).length;
                        correct = Object.keys(st.correctness || {}).filter(k => st.correctness[k]).length;
                    } catch(e) {}
                }
                const card = document.getElementById('quiz-select-' + qId);
                if (card) {
                    const pctEl = card.querySelector('.quiz-select-progress');
                    if (pctEl) {
                        if (progress > 0) {
                            pctEl.innerText = progress === total ? `Completed — ${correct}/${total} correct` : `${progress}/${total} answered`;
                            pctEl.classList.remove('hidden');
                        } else {
                            pctEl.innerText = 'Not started';
                            pctEl.classList.remove('hidden');
                        }
                    }
                }
            });
        }

        function updatePassageHeader(quizId) {
            const titleEl = document.getElementById('passage-main-title');
            const subtitleEl = document.getElementById('passage-subtitle');
            if (!titleEl || !subtitleEl) return;

            if (quizId === 'quiz1') {
                titleEl.innerText = "Quiz 1";
                subtitleEl.innerText = "Reading Comprehension";
            } else if (quizId === 'quiz3') {
                titleEl.innerText = "Quiz 2";
                subtitleEl.innerText = "Sentence Completion & Equivalence";
            } else if (quizId === 'quiz2') {
                titleEl.innerText = "Quiz 3";
                subtitleEl.innerText = "Full Verbal Reasoning";
            }
        }

        function selectQuiz(quizId) {
            switchActiveQuiz(quizId);
            document.getElementById('passage-quiz-selector').classList.add('hidden');
            document.getElementById('passage-reset-btn').classList.remove('hidden');
            
            loadPassageState();
            updatePassageHeader(quizId);
            
            if (isPassageQuizComplete()) {
                showPassageScoreScreen();
            } else {
                let firstUnsubmitted = 0;
                while (firstUnsubmitted < passageData.questions.length && passageState.submitted[passageData.questions[firstUnsubmitted].id]) {
                    firstUnsubmitted++;
                }
                if (firstUnsubmitted < passageData.questions.length) {
                    passageState.currentIdx = firstUnsubmitted;
                } else {
                    passageState.currentIdx = 0;
                }
                
                document.getElementById('passage-quiz-container').classList.remove('hidden');
                document.getElementById('passage-quiz-container').classList.add('flex');
                document.getElementById('passage-results-container').classList.add('hidden');
                
                renderPassageQuestion(passageState.currentIdx);
            }
        }

        function passageBack() {
            const selector = document.getElementById('passage-quiz-selector');
            // If quiz selector is already showing, go back to main menu
            if (!selector.classList.contains('hidden')) {
                _navStack = ['setup-screen'];
                _showScreen('setup-screen');
                return;
            }
            // Otherwise go back to quiz selector
            showQuizSelector();
        }

        function renderPassageQuestion(index) {
            passageState.currentIdx = index;
            savePassageState();
            
            const question = passageData.questions[index];
            selectedSentencePos = null;
            
            if (question.passageBased) {
                document.getElementById('passage-pane-title').innerText = "Reading Passage";
                renderPassageTextContent(question.type === 'sentence');
            } else {
                document.getElementById('passage-pane-title').innerText = question.promptLabel || "PARAGRAPH ARGUMENT";
                document.getElementById('passage-scroll-container').innerHTML = `
                    <p class="mb-4 text-justify leading-relaxed font-sans text-slate-700 dark:text-slate-300 text-base sm:text-[17px] select-text">
                        ${question.prompt}
                    </p>
                `;
            }
            
            document.getElementById('passage-question-text').innerText = question.question;
            
            const optionsContainer = document.getElementById('passage-options-container');
            optionsContainer.innerHTML = '';
            
            const isSubmitted = passageState.submitted[question.id];
            const savedAnswer = passageState.answers[question.id];
            
            if (question.type === 'single') {
                question.options.forEach((opt, oIdx) => {
                    const btn = document.createElement('button');
                    btn.className = "w-full text-left p-3.5 rounded-xl border font-sans text-sm sm:text-[15px] font-medium transition-all duration-155 flex items-start gap-3 select-none text-black dark:text-white";
                    
                    const isSelected = savedAnswer === oIdx;
                    
                    if (isSubmitted) {
                        btn.disabled = true;
                        const isCorrect = oIdx === question.answer;
                        if (isCorrect) {
                            btn.className += " border-emerald-500 bg-emerald-50 dark:bg-emerald-950/20 text-black dark:text-white";
                        } else if (isSelected) {
                            btn.className += " border-rose-500 bg-rose-50 dark:bg-rose-950/20 text-black dark:text-white";
                        } else {
                            btn.className += " border-slate-200 dark:border-neutral-800 text-slate-400 dark:text-slate-500";
                        }
                    } else {
                        if (isSelected) {
                            btn.className += " border-primary-600 bg-primary-50 dark:bg-primary-950/20 text-black dark:text-white ring-2 ring-primary-500/35";
                        } else {
                            btn.className += " border-slate-200 dark:border-neutral-800 bg-white dark:bg-neutral-900 hover:bg-slate-50 dark:hover:bg-neutral-800 text-black dark:text-white";
                        }
                        
                        btn.onclick = () => {
                            passageState.answers[question.id] = oIdx;
                            savePassageState();
                            renderPassageQuestion(index);
                        };
                    }
                    
                    const badge = document.createElement('span');
                    badge.className = `inline-flex items-center justify-center w-5 h-5 rounded-full text-xs font-bold shrink-0 ${
                        isSelected 
                            ? 'bg-primary-600 text-white' 
                            : isSubmitted && oIdx === question.answer
                                ? 'bg-emerald-600 text-white'
                                : isSubmitted && isSelected
                                    ? 'bg-rose-600 text-white'
                                    : 'bg-slate-100 dark:bg-neutral-800 text-slate-500 dark:text-slate-400'
                    }`;
                    badge.innerText = String.fromCharCode(65 + oIdx);
                    
                    btn.appendChild(badge);
                    
                    const textEl = document.createElement('span');
                    textEl.innerText = opt;
                    btn.appendChild(textEl);
                    
                    optionsContainer.appendChild(btn);
                });
            } else if (question.type === 'multiple') {
                question.options.forEach((opt, oIdx) => {
                    const btn = document.createElement('button');
                    btn.className = "w-full text-left p-3.5 rounded-xl border font-sans text-sm sm:text-[15px] font-medium transition-all duration-155 flex items-start gap-3 select-none text-black dark:text-white";
                    
                    const isSelected = Array.isArray(savedAnswer) && savedAnswer.includes(oIdx);
                    const isCorrectOption = question.answer.includes(oIdx);
                    
                    if (isSubmitted) {
                        btn.disabled = true;
                        if (isCorrectOption) {
                            btn.className += " border-emerald-500 bg-emerald-50 dark:bg-emerald-950/20 text-black dark:text-white";
                        } else if (isSelected) {
                            btn.className += " border-rose-500 bg-rose-50 dark:bg-rose-950/20 text-black dark:text-white";
                        } else {
                            btn.className += " border-slate-200 dark:border-neutral-800 text-slate-400 dark:text-slate-500";
                        }
                    } else {
                        if (isSelected) {
                            btn.className += " border-primary-600 bg-primary-50 dark:bg-primary-950/20 text-black dark:text-white ring-2 ring-primary-500/35";
                        } else {
                            btn.className += " border-slate-200 dark:border-neutral-800 bg-white dark:bg-neutral-900 hover:bg-slate-50 dark:hover:bg-neutral-800 text-black dark:text-white";
                        }
                        
                        btn.onclick = () => {
                            let currentAnswers = passageState.answers[question.id] || [];
                            if (!Array.isArray(currentAnswers)) currentAnswers = [];
                            if (currentAnswers.includes(oIdx)) {
                                currentAnswers = currentAnswers.filter(x => x !== oIdx);
                            } else {
                                currentAnswers.push(oIdx);
                            }
                            passageState.answers[question.id] = currentAnswers;
                            savePassageState();
                            renderPassageQuestion(index);
                        };
                    }
                    
                    const badge = document.createElement('span');
                    badge.className = `inline-flex items-center justify-center w-5 h-5 rounded text-[10px] font-bold shrink-0 ${
                        isSelected 
                            ? 'bg-primary-600 text-white' 
                            : isSubmitted && isCorrectOption
                                ? 'bg-emerald-600 text-white'
                                : isSubmitted && isSelected
                                    ? 'bg-rose-600 text-white'
                                    : 'bg-slate-100 dark:bg-neutral-800 text-slate-500 dark:text-slate-400'
                    }`;
                    badge.innerHTML = isSelected || (isSubmitted && isCorrectOption) 
                        ? `<svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2.5" d="M5 13l4 4L19 7"></path></svg>` 
                        : String.fromCharCode(65 + oIdx);
                    
                    btn.appendChild(badge);
                    
                    const textEl = document.createElement('span');
                    textEl.innerText = opt;
                    btn.appendChild(textEl);
                    
                    optionsContainer.appendChild(btn);
                });
            } else if (question.type === 'sentence') {
                const helper = document.createElement('div');
                helper.className = "p-4 rounded-xl border border-dashed border-amber-300 dark:border-amber-900/60 bg-amber-50/50 dark:bg-amber-950/20 text-amber-800 dark:text-amber-300 text-xs sm:text-sm leading-relaxed flex gap-3";
                helper.innerHTML = `
                    <svg class="w-5 h-5 shrink-0 text-amber-500" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                        <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M13 16h-1v-4h-1m1-4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z"></path>
                    </svg>
                    <div>
                        ${isSubmitted 
                            ? "<strong>Sentence Selection Completed.</strong> Review the highlighted passage text on the left." 
                            : "<strong>Action Required:</strong> Click on the sentence in the reading passage on the left that best answers the question."}
                    </div>
                `;
                optionsContainer.appendChild(helper);
                
                if (savedAnswer) {
                    const selectedPreview = document.createElement('div');
                    if (isSubmitted) {
                        const isCorrect = passageState.correctness[question.id];
                        selectedPreview.className = `p-3.5 rounded-xl border text-xs sm:text-sm font-medium text-white shadow-sm ${
                            isCorrect
                                ? 'border-emerald-600 bg-emerald-600 dark:bg-emerald-700'
                                : 'border-rose-600 bg-rose-600 dark:bg-rose-700'
                        }`;
                        selectedPreview.innerHTML = `
                            <div class="text-[10px] uppercase font-bold text-white/70 mb-1 tracking-wider">
                                Selected Sentence
                            </div>
                            <div class="italic text-white text-sm sm:text-base font-semibold leading-relaxed">"${savedAnswer}"</div>
                        `;
                    } else {
                        selectedPreview.className = "p-3.5 rounded-xl border border-slate-250 dark:border-neutral-800 bg-transparent shadow-sm";
                        selectedPreview.innerHTML = `
                            <div class="text-[10px] uppercase font-bold text-slate-400 dark:text-slate-500 mb-1 tracking-wider">
                                Selected Sentence
                            </div>
                            <div class="italic text-slate-800 dark:text-slate-200 text-base sm:text-lg font-semibold leading-relaxed">"${savedAnswer}"</div>
                        `;
                    }
                    optionsContainer.appendChild(selectedPreview);
                }
            } else if (question.type === 'two_blank' || question.type === 'three_blank') {
                // Multi-blank Text Completion
                const blanks = question.blanks;
                const numBlanks = blanks.length;
                const gridCols = numBlanks === 2 ? 'grid-cols-2' : 'grid-cols-3';
                
                const wrapper = document.createElement('div');
                wrapper.className = `grid ${gridCols} gap-3`;
                
                blanks.forEach((blank, bIdx) => {
                    const col = document.createElement('div');
                    col.className = 'space-y-2';
                    
                    const label = document.createElement('div');
                    label.className = 'text-xs font-bold text-slate-500 dark:text-slate-400 uppercase tracking-wider pb-1 border-b border-slate-200 dark:border-neutral-700 mb-1';
                    label.innerText = blank.label;
                    col.appendChild(label);
                    
                    blank.options.forEach((opt, oIdx) => {
                        const btn = document.createElement('button');
                        btn.className = 'w-full text-left p-2.5 rounded-lg border font-sans text-xs sm:text-sm font-medium transition-all duration-150 flex items-start gap-2 select-none text-black dark:text-white';
                        
                        const currentAnswers = Array.isArray(savedAnswer) ? savedAnswer : [];
                        const isSelected = currentAnswers[bIdx] === oIdx;
                        const correctVal = question.answer[bIdx];
                        
                        if (isSubmitted) {
                            btn.disabled = true;
                            if (oIdx === correctVal) {
                                btn.className += ' border-emerald-500 bg-emerald-50 dark:bg-emerald-950/20';
                            } else if (isSelected) {
                                btn.className += ' border-rose-500 bg-rose-50 dark:bg-rose-950/20';
                            } else {
                                btn.className += ' border-slate-200 dark:border-neutral-800 text-slate-400 dark:text-slate-500';
                            }
                        } else {
                            if (isSelected) {
                                btn.className += ' border-primary-600 bg-primary-50 dark:bg-primary-950/20 ring-2 ring-primary-500/35';
                            } else {
                                btn.className += ' border-slate-200 dark:border-neutral-800 bg-white dark:bg-neutral-900 hover:bg-slate-50 dark:hover:bg-neutral-800';
                            }
                            btn.onclick = () => {
                                let answers = Array.isArray(passageState.answers[question.id]) ? [...passageState.answers[question.id]] : new Array(numBlanks).fill(undefined);
                                answers[bIdx] = oIdx;
                                passageState.answers[question.id] = answers;
                                savePassageState();
                                renderPassageQuestion(index);
                            };
                        }
                        
                        const badge = document.createElement('span');
                        badge.className = `inline-flex items-center justify-center w-4 h-4 rounded-full text-[10px] font-bold shrink-0 ${
                            isSelected ? 'bg-primary-600 text-white' 
                            : isSubmitted && oIdx === correctVal ? 'bg-emerald-600 text-white'
                            : 'bg-slate-100 dark:bg-neutral-800 text-slate-500 dark:text-slate-400'
                        }`;
                        badge.innerText = String.fromCharCode(65 + (bIdx * 3) + oIdx);
                        btn.appendChild(badge);
                        
                        const textEl = document.createElement('span');
                        textEl.innerText = opt;
                        btn.appendChild(textEl);
                        
                        col.appendChild(btn);
                    });
                    
                    wrapper.appendChild(col);
                });
                
                optionsContainer.appendChild(wrapper);
            } else if (question.type === 'sentence_equiv') {
                // Sentence Equivalence - select exactly 2
                const helper = document.createElement('div');
                helper.className = 'p-3 rounded-lg border border-dashed border-primary-300 dark:border-primary-900/60 bg-primary-50/50 dark:bg-primary-950/20 text-primary-800 dark:text-primary-300 text-xs leading-relaxed mb-2 flex gap-2 items-center';
                helper.innerHTML = `<svg class="w-4 h-4 shrink-0" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M13 16h-1v-4h-1m1-4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z"></path></svg><span>Select exactly <strong>two</strong> answer choices.</span>`;
                optionsContainer.appendChild(helper);
                
                question.options.forEach((opt, oIdx) => {
                    const btn = document.createElement('button');
                    btn.className = 'w-full text-left p-3.5 rounded-xl border font-sans text-sm sm:text-[15px] font-medium transition-all duration-155 flex items-start gap-3 select-none text-black dark:text-white';
                    
                    const isSelected = Array.isArray(savedAnswer) && savedAnswer.includes(oIdx);
                    const isCorrectOption = question.answer.includes(oIdx);
                    
                    if (isSubmitted) {
                        btn.disabled = true;
                        if (isCorrectOption) {
                            btn.className += ' border-emerald-500 bg-emerald-50 dark:bg-emerald-950/20';
                        } else if (isSelected) {
                            btn.className += ' border-rose-500 bg-rose-50 dark:bg-rose-950/20';
                        } else {
                            btn.className += ' border-slate-200 dark:border-neutral-800 text-slate-400 dark:text-slate-500';
                        }
                    } else {
                        if (isSelected) {
                            btn.className += ' border-primary-600 bg-primary-50 dark:bg-primary-950/20 ring-2 ring-primary-500/35';
                        } else {
                            btn.className += ' border-slate-200 dark:border-neutral-800 bg-white dark:bg-neutral-900 hover:bg-slate-50 dark:hover:bg-neutral-800';
                        }
                        btn.onclick = () => {
                            let currentAnswers = passageState.answers[question.id] || [];
                            if (!Array.isArray(currentAnswers)) currentAnswers = [];
                            if (currentAnswers.includes(oIdx)) {
                                currentAnswers = currentAnswers.filter(x => x !== oIdx);
                                passageState.answers[question.id] = currentAnswers;
                                savePassageState();
                                renderPassageQuestion(index);
                            } else {
                                if (currentAnswers.length >= 2) {
                                    // Block selection, play haptic, and shake
                                    haptic();
                                    btn.classList.add('animate-shake');
                                    setTimeout(() => {
                                        btn.classList.remove('animate-shake');
                                    }, 350);
                                } else {
                                    currentAnswers.push(oIdx);
                                    passageState.answers[question.id] = currentAnswers;
                                    savePassageState();
                                    renderPassageQuestion(index);
                                }
                            }
                        };
                    }
                    
                    const badge = document.createElement('span');
                    badge.className = `inline-flex items-center justify-center w-5 h-5 rounded text-[10px] font-bold shrink-0 ${
                        isSelected ? 'bg-primary-600 text-white'
                        : isSubmitted && isCorrectOption ? 'bg-emerald-600 text-white'
                        : 'bg-slate-100 dark:bg-neutral-800 text-slate-500 dark:text-slate-400'
                    }`;
                    badge.innerHTML = isSelected || (isSubmitted && isCorrectOption)
                        ? `<svg class="w-3.5 h-3.5" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2.5" d="M5 13l4 4L19 7"></path></svg>`
                        : String.fromCharCode(65 + oIdx);
                    btn.appendChild(badge);
                    
                    const textEl = document.createElement('span');
                    textEl.innerText = opt;
                    btn.appendChild(textEl);
                    
                    optionsContainer.appendChild(btn);
                });
            }
            
            const explContainer = document.getElementById('passage-explanation-container');
            const submitBtn = document.getElementById('passage-submit-btn');
            const nextBtn = document.getElementById('passage-next-btn');
            
            if (isSubmitted) {
                explContainer.classList.remove('hidden');
                
                const isCorrect = passageState.correctness[question.id];
                const badge = document.getElementById('passage-feedback-badge');
                
                if (isCorrect) {
                    badge.innerText = "Correct";
                    badge.className = "px-3 py-1 rounded-full text-xs font-bold uppercase tracking-wider bg-emerald-100 dark:bg-emerald-900/40 text-emerald-800 dark:text-emerald-300 border border-emerald-250 dark:border-emerald-900/50";
                    explContainer.className = "mt-6 p-4 rounded-xl border border-emerald-200 dark:border-emerald-900/40 bg-emerald-50/20 dark:bg-emerald-950/10 transition-all duration-300";
                } else {
                    badge.innerText = "Incorrect";
                    badge.className = "px-3 py-1 rounded-full text-xs font-bold uppercase tracking-wider bg-rose-100 dark:bg-rose-900/40 text-rose-800 dark:text-rose-300 border border-rose-250 dark:border-rose-900/50";
                    explContainer.className = "mt-6 p-4 rounded-xl border border-rose-200 dark:border-rose-900/40 bg-rose-50/20 dark:bg-rose-950/10 transition-all duration-300";
                }
                
                document.getElementById('passage-explanation-text').innerText = question.explanation;
                submitBtn.classList.add('hidden');
            } else {
                explContainer.classList.add('hidden');
                submitBtn.classList.remove('hidden');
                
                let hasSelection = false;
                if (question.type === 'sentence') {
                    hasSelection = !!savedAnswer;
                } else if (question.type === 'single') {
                    hasSelection = savedAnswer !== undefined;
                } else if (question.type === 'two_blank' || question.type === 'three_blank') {
                    const numBlanks = question.blanks.length;
                    hasSelection = Array.isArray(savedAnswer) && savedAnswer.length === numBlanks && savedAnswer.every(v => v !== undefined);
                } else if (question.type === 'sentence_equiv') {
                    hasSelection = Array.isArray(savedAnswer) && savedAnswer.length === 2;
                } else {
                    hasSelection = Array.isArray(savedAnswer) && savedAnswer.length > 0;
                }
                submitBtn.disabled = !hasSelection;
            }
            
            // Next Button Setup (Always Visible)
            if (index < passageData.questions.length - 1) {
                nextBtn.innerText = "Next";
                nextBtn.onclick = passageNextQuestion;
                nextBtn.disabled = false;
            } else {
                nextBtn.innerText = "Finish Quiz";
                nextBtn.onclick = showPassageScoreScreen;
                nextBtn.disabled = !isPassageQuizComplete();
            }
            
            document.getElementById('passage-prev-btn').disabled = index === 0;
            
            renderPassageProgressDots();
        }

        function renderPassageTextContent(interactive = false) {
            const container = document.getElementById('passage-scroll-container');
            container.innerHTML = '';
            
            const question = passageData.questions[passageState.currentIdx];
            const isSubmitted = passageState.submitted[question.id];
            const savedAnswer = passageState.answers[question.id];
            
            passageData.passageParagraphs.forEach((paragraph, pIdx) => {
                const pEl = document.createElement('p');
                pEl.className = "mb-4 text-justify leading-relaxed";
                
                paragraph.forEach((sentence, sIdx) => {
                    const span = document.createElement('span');
                    span.innerText = sentence + " ";
                    span.className = "passage-sentence transition-all duration-200 rounded px-1 -mx-1 py-0.5 inline";
                    span.dataset.paragraph = pIdx;
                    span.dataset.sentence = sIdx;
                    
                    const isSelected = savedAnswer === sentence;
                    
                    if (isSubmitted) {
                        const isCorrectSentence = sentence === question.answer;
                        if (isCorrectSentence) {
                            span.className += " bg-emerald-100 dark:bg-emerald-950/60 ring-2 ring-emerald-500 text-emerald-950 dark:text-emerald-100 font-medium";
                        } else if (isSelected) {
                            span.className += " bg-rose-100 dark:bg-rose-950/60 ring-2 ring-rose-500 text-rose-950 dark:text-rose-100";
                        }
                    } else if (interactive) {
                        span.className += " cursor-pointer hover:bg-primary-50/50 dark:hover:bg-primary-950/20 hover:text-black dark:hover:text-white";
                        
                        if (isSelected) {
                            span.className += " bg-primary-50 dark:bg-primary-950/30 ring-2 ring-amber-500 text-black dark:text-white font-medium";
                        }
                        
                        span.onclick = () => {
                            selectSentence(span);
                        };
                    }
                    
                    pEl.appendChild(span);
                });
                
                container.appendChild(pEl);
            });
        }
 
        function selectSentence(span) {
            const question = passageData.questions[passageState.currentIdx];
            
            document.querySelectorAll('.passage-sentence').forEach(el => {
                el.classList.remove('bg-primary-50', 'dark:bg-primary-950/30', 'ring-2', 'ring-amber-500', 'text-black', 'dark:text-white', 'font-medium');
            });
            
            span.className += " bg-primary-50 dark:bg-primary-950/30 ring-2 ring-amber-500 text-black dark:text-white font-medium";
            
            const sentenceText = span.innerText.trim();
            passageState.answers[question.id] = sentenceText;
            savePassageState();
            
            renderPassageQuestion(passageState.currentIdx);
        }

        function submitPassageAnswer() {
            haptic();
            const question = passageData.questions[passageState.currentIdx];
            const answer = passageState.answers[question.id];
            
            let isCorrect = false;
            
            if (question.type === 'single') {
                isCorrect = answer === question.answer;
            } else if (question.type === 'multiple' || question.type === 'sentence_equiv') {
                if (Array.isArray(answer) && Array.isArray(question.answer)) {
                    isCorrect = answer.length === question.answer.length &&
                                answer.every(x => question.answer.includes(x)) &&
                                question.answer.every(x => answer.includes(x));
                }
            } else if (question.type === 'sentence') {
                isCorrect = answer === question.answer;
            } else if (question.type === 'two_blank' || question.type === 'three_blank') {
                if (Array.isArray(answer) && Array.isArray(question.answer)) {
                    isCorrect = answer.length === question.answer.length &&
                                answer.every((v, i) => v === question.answer[i]);
                }
            }
            
            passageState.submitted[question.id] = true;
            passageState.correctness[question.id] = isCorrect;
            savePassageState();
            renderPassageQuestion(passageState.currentIdx);
            
            // Custom smooth scroll animation that is lightweight (no layout thrashing) and fast
            function smoothScrollToBottom(element) {
                if (!element) return;
                const start = element.scrollTop;
                const target = element.scrollHeight - element.clientHeight;
                if (target <= start) return;
                
                const duration = 250; // ms (snappy transition)
                const startTime = performance.now();
                
                function animate(currentTime) {
                    const elapsed = currentTime - startTime;
                    const progress = Math.min(elapsed / duration, 1);
                    
                    // Ease-out quad for snappy initial acceleration
                    const ease = progress * (2 - progress);
                    
                    element.scrollTop = start + (target - start) * ease;
                    
                    if (progress < 1) {
                        requestAnimationFrame(animate);
                    }
                }
                requestAnimationFrame(animate);
            }

            // Scroll both main container (for mobile) and question container (for desktop)
            setTimeout(() => {
                const mainEl = document.querySelector('main');
                const questionContainer = document.getElementById('passage-question-card')?.parentElement;
                
                if (mainEl) smoothScrollToBottom(mainEl);
                if (questionContainer) smoothScrollToBottom(questionContainer);
                
                // Backup scroll for document/body just in case
                smoothScrollToBottom(document.documentElement);
                smoothScrollToBottom(document.body);
            }, 50);
        }

        function passageNextQuestion() {
            haptic();
            if (passageState.currentIdx < passageData.questions.length - 1) {
                renderPassageQuestion(passageState.currentIdx + 1);
            }
        }

        function passagePrevQuestion() {
            haptic();
            if (passageState.currentIdx > 0) {
                renderPassageQuestion(passageState.currentIdx - 1);
            }
        }

        function renderPassageProgressDots() {
            const container = document.getElementById('passage-progress-dots');
            container.innerHTML = '';
            
            passageData.questions.forEach((q, idx) => {
                const dot = document.createElement('button');
                
                const isCurrent = idx === passageState.currentIdx;
                const isSubmitted = passageState.submitted[q.id];
                const isCorrect = passageState.correctness[q.id];
                
                dot.className = "w-7 h-7 rounded-lg text-xs font-bold transition-all flex items-center justify-center border ";
                
                if (isCurrent) {
                    dot.className += "border-primary-600 bg-primary-50 dark:bg-primary-950/40 text-primary-700 dark:text-primary-400 ring-2 ring-primary-500/25";
                } else if (isSubmitted) {
                    if (isCorrect) {
                        dot.className += "border-emerald-500 bg-emerald-500 text-white dark:bg-emerald-950/40 dark:text-emerald-400";
                    } else {
                        dot.className += "border-rose-500 bg-rose-500 text-white dark:bg-rose-950/40 dark:text-rose-400";
                    }
                } else {
                    dot.className += "border-slate-200 dark:border-neutral-800 bg-slate-100 dark:bg-neutral-900 text-slate-500 dark:text-slate-400 hover:bg-slate-200 dark:hover:bg-neutral-800";
                }
                
                dot.innerText = idx + 1;
                
                dot.onclick = () => {
                    haptic();
                    document.getElementById('passage-quiz-container').classList.remove('hidden');
                    document.getElementById('passage-quiz-container').classList.add('flex');
                    document.getElementById('passage-results-container').classList.add('hidden');
                    renderPassageQuestion(idx);
                };
                
                container.appendChild(dot);
            });
        }

        function showPassageScoreScreen() {
            document.getElementById('passage-quiz-container').classList.add('hidden');
            document.getElementById('passage-quiz-container').classList.remove('flex');
            document.getElementById('passage-results-container').classList.remove('hidden');
            document.getElementById('passage-reset-btn').classList.remove('hidden');
            
            let score = 0;
            passageData.questions.forEach(q => {
                if (passageState.correctness[q.id]) score++;
            });
            
            const total = passageData.questions.length;
            const pct = Math.round((score / total) * 100);
            
            document.getElementById('passage-results-score').innerText = `${score} / ${total}`;
            document.getElementById('passage-results-pct').innerText = `${pct}%`;
            
            const reviewList = document.getElementById('passage-review-list');
            reviewList.innerHTML = '';
            
            passageData.questions.forEach((q, idx) => {
                const item = document.createElement('div');
                item.className = "flex items-center p-3 rounded-xl border border-slate-200/60 dark:border-neutral-800 bg-slate-50 dark:bg-neutral-900/50 hover:bg-slate-100 dark:hover:bg-neutral-800/50 cursor-pointer transition-all duration-150 gap-3";
                
                const isCorrect = passageState.correctness[q.id];
                const displayQuestion = q.question.length > 45 ? q.question.substring(0, 42) + '...' : q.question;
                
                item.innerHTML = `
                    <div class="flex items-center gap-3 w-full">
                        <span class="flex-shrink-0 w-6 h-6 rounded-md flex items-center justify-center text-xs font-bold ${
                            isCorrect 
                                ? 'bg-emerald-100 dark:bg-emerald-950/40 text-emerald-700 dark:text-emerald-400 border border-emerald-250 dark:border-emerald-900/50' 
                                : 'bg-rose-100 dark:bg-rose-950/40 text-rose-700 dark:text-rose-400 border border-rose-250 dark:border-rose-900/50'
                        }">
                            ${idx + 1}
                        </span>
                        <div class="text-xs sm:text-sm font-semibold text-slate-700 dark:text-slate-300 truncate">
                            ${displayQuestion}
                        </div>
                    </div>
                `;
                
                item.onclick = () => {
                    haptic();
                    document.getElementById('passage-quiz-container').classList.remove('hidden');
                    document.getElementById('passage-quiz-container').classList.add('flex');
                    document.getElementById('passage-results-container').classList.add('hidden');
                    renderPassageQuestion(idx);
                };
                
                reviewList.appendChild(item);
            });
        }

        function resetPassageProgress() {
            haptic();
            if (confirm("Are you sure you want to reset your quiz progress and start over?")) {
                resetPassageStateNoConfirm();
                document.getElementById('passage-quiz-container').classList.remove('hidden');
                document.getElementById('passage-quiz-container').classList.add('flex');
                document.getElementById('passage-results-container').classList.add('hidden');
                renderPassageQuestion(0);
            }
        }



        // URL Parameter Routing on Page Load
        function checkUrlRouting() {
            const urlParams = new URLSearchParams(window.location.search);
            const screen = urlParams.get('screen');
            if (screen === 'library') {
                goToLibrary();
            } else if (screen === 'passage') {
                goToPassageMode();
            }
        }

        document.addEventListener('DOMContentLoaded', () => {
            initHapticOverlays();
            checkUrlRouting();
        });
        if (document.readyState !== 'loading') {
            initHapticOverlays();
            checkUrlRouting();
        }